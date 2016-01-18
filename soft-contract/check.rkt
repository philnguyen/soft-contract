#lang typed/racket/base
(provide analyze try-verify try-refute
         exn:fail:contract:counterexample exn:fail:contract:counterexample?
         exn:fail:contract:maybe exn:fail:contract:maybe?
         exn:scv exn:scv?)
(require
 racket/match racket/list racket/port racket/string racket/set
 racket/pretty

 "utils/def.rkt" "utils/untyped-macros.rkt" "utils/pretty.rkt" "utils/set.rkt"
 "ast/definition.rkt"
 "runtime/val.rkt"
 ;; For verification
 (prefix-in ve: "widened.rkt")
 ;; For counter-exapmle
 (prefix-in ce: "refute.rkt")
 )

;; Raise different exceptions for definite counterexample and probable contract violation
(struct exn:fail:contract:counterexample exn:fail:contract () #:transparent)
(struct exn:fail:contract:maybe exn:fail:contract () #:transparent)
(struct exn:fail:timeout exn:fail () #:transparent)
(define-type exn:scv (U exn:fail:contract:maybe exn:fail:contract:counterexample))
(define-predicate exn:scv? exn:scv)

(define-type Err-Result (List 'blame Mon-Party Mon-Party Any Any))
(define-data Result
  'timeout
  (subset: Ce-Result
           'safe
           Err-Result
           (List 'ce Err-Result Any)
           exn)
  (subset: Ve-Result
           (Listof Err-Result)
           exn))

(: analyze ([Path-String] [#:timeout Integer #:timeout-ok? Boolean] . ->* . Void))
;; Analyze program at given path
(define (analyze path #:timeout [timeout 60] #:timeout-ok? [timeout-ok? #t])
  (match (run path timeout)
    ['timeout
     (define msg (format "Timeout after ~a seconds~n" timeout))
     (cond [timeout-ok? (printf msg)]
           [else (raise (exn:fail:timeout msg (current-continuation-marks)))])]
    [(or 'safe (list)) (printf "Program is safe~n")]
    [(list 'blame l+ lo v c)
     (raise-scv-contract-error l+ lo v c)]
    [(list 'ce (list 'blame l+ lo v c) ce)
     (raise-scv-contract-error l+ lo v c ce)]
    [(cons (list 'blame l+ lo v c) _) ; Raise first error
     (raise-scv-contract-error l+ lo v c)]
    [(? exn? e)
     (error (exn-message e))]))

(: run : Path-String Integer → Result)
;; Concurrently verify + seek counterexamples in given time
(define (run path timeout)
  (define c : (Channelof Result) (make-channel))
  (define verify-thread (thread (λ () (channel-put c (try-verify path)))))
  (define refute-thread (thread (λ () (channel-put c (try-refute path)))))
  (define timeout-thread (thread (λ () (sleep timeout) (channel-put c 'timeout))))
  
  (define (kill-all)
    (for-each kill-thread (list verify-thread refute-thread timeout-thread)))
  
  (match (channel-get c)
    [(and err (or (cons 'blame _) (cons (cons 'blame _) _)))
     ;; Wait for (probable) counter-example, unless timeout
     (match (channel-get c)
       ['timeout (kill-all) err]
       [res (kill-all) res])]
    [res (kill-all) res]))

(: try-verify : Path-String → Ve-Result)
;; Attempt to verify correct program or warn about probable contract violation
(define (try-verify path)
  (with-handlers ([exn:fail? (λ ([e : exn]) e)])
    (define-values (_t Cfgs _σ _Ξ _M) (ve:verify-files path))

    (remove-duplicates
     (for/list : (Listof Err-Result)
               ([Cfg Cfgs] #:when (match? Cfg (ve:-Cfg (? -blm?) _ _)))
       (match-define (ve:-Cfg (-blm l+ lo C Vs) _ _) Cfg)
       (list 'blame l+ lo (show-V C) (map show-V Vs))))))

(: dbg-verify : Path-String → (U (Listof ve:-Cfg) exn))
(define (dbg-verify path)
  (with-handlers ([exn:fail? (λ ([e : exn]) e)])
    (define-values (_t Cfgs _σ _Ξ _M) (ve:verify-files path))
    (set->list Cfgs)))

(: try-refute : Path-String → Ce-Result)
;; Attempt to search for erroneous inputs, or prove absence of one in rare cases
(define (try-refute path)
  (with-handlers ([exn:fail? (λ ([e : exn]) e)])
    (cond
      [(ce:refute-files path) =>
       (match-lambda
         [(cons (-blm l+ lo C Vs) e†)
          (if e†
              (list 'ce (list 'blame l+ lo (show-V C) (map show-V Vs)) (show-e e†))
              (list 'blame l+ lo (show-V C) (map show-V Vs)))])]
      [else 'safe])))

(: raise-scv-contract-error ([Any Any Any Any] [Any] . ->* . Nothing))
;; FIXME: fix stuff with `replace-struct-●`
(define (raise-scv-contract-error l+ lo v c [ce #f])
  (define sure? #t)
  
  (define parties
    (cond [(equal? l+ lo) (format "'~a' violates its own contract." l+)]
          [(equal? lo 'Λ) (format "'~a' violates a contract in an application." l+)]
          [else (format "'~a' violates '~a'." l+ lo)]))
  
  (define reason : String
    (match c
      [`(arity=/c ,_) "Wrong arity"]
      [_ (format "Value~n ~a~nviolates predicate~n ~a" (pretty v) (pretty c))]))
  
  (define ce-prog
    (cond [ce (format "An example module that breaks it:~n ~a"
                      (pretty `(module user racket
                                 (require (submod "\"..\"" ,l+))
                                 ce)))]
          [else ""]))

  (cond [sure? (raise-counterexample parties reason ce-prog)]
        [else (raise-maybe-contract-violation parties reason)]))

(define (raise-counterexample [parties : String] [reason : String] [ce : String]) : Nothing
  (raise (exn:fail:contract:counterexample
          (format "Contract violation: ~a~n~a~n~a~n"
                  parties
                  reason
                  ce)
          (current-continuation-marks))))

(define (raise-maybe-contract-violation [parties : String] [reason : String]) : Nothing
  (raise (exn:fail:contract:maybe
          (format "Possible contract violation: ~a~n~a~n"
                  parties
                  reason)
          (current-continuation-marks))))

(: replace-struct● : Any → Any)
;; Traverse the S-exp, replace all (struct● _) and insert top-level struct definitions
(define (replace-struct● e)

  (define-set new-names : Symbol)
  
  (define e*
    (let go! : Any ([e : Any e])
      (match e
        [`(struct● ,tag)
         (define name (string->symbol (format "s~a" (n-sub (assert tag exact-integer?)))))
         (new-names-add! name)
         `(,name)]
        [(list xs ...) (map go! xs)]
        [_ e])))
  
  (-begin
   `(,@(for/list : (Listof Any) ([name (in-set new-names)])
         `(struct ,name ()))
     ,e*)))
