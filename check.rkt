#lang typed/racket/base
(provide feedback)
(require racket/match racket/list racket/port racket/string racket/set
         racket/pretty
         (only-in "utils.rkt" match? pretty n-sub define-set)
         (only-in "lang.rkt" .prog -begin Mon-Party)
         (only-in "machine.rkt" .ς)
         (only-in "verify/machine.rkt" [ev verify])
         (only-in "runtime.rkt" .blm? .blm .σ .σ?)
         (only-in "show.rkt" show-V show-A show-ce)
         (only-in "ce/machine.rkt" [ev find-error])
         (only-in "ce/model.rkt" model))

(: feedback ([.prog] [Integer] . ->* . Void))
(define (feedback prog [timeout 30])
  (eprintf ">>> program is:\n")
  (pretty-print prog (current-error-port))
  (match (run prog timeout)
    ['timeout (printf "Timeout after ~a seconds~n" timeout)]
    [(or 'safe (list)) (printf "Program is safe~n")]
    [(list 'blame l⁺ lᵒ v c)
     (raise-contract-error l⁺ lᵒ v c)]
    [(list 'ce (list 'blame l⁺ lᵒ v c) ce)
     (raise-contract-error l⁺ lᵒ v c ce)]
    [(? exn? e)
     (error (exn-message e))]
    [(cons (list 'blame l⁺ lᵒ v c) _)
     ;; Raise first error
     (raise-contract-error l⁺ lᵒ v c)]))

(define-type Result (U 'timeout Ce-Result Ve-Result))
(define-type Ce-Result (U 'safe Err-Result (List 'ce Err-Result Any) exn))
(define-type Ve-Result (U (Listof Err-Result) exn))
(define-type Err-Result (List 'blame Mon-Party Mon-Party Any Any))

(: run : .prog Integer → Result)
;; Verify + Seek counterexamples at the same time, whichever finishes first
(define (run prog timeout)
  (define c : (Channelof Result) (make-channel))
  (define verify-thread (thread (λ () (channel-put c (try-verify prog)))))
  (define ce-thread (thread (λ () (channel-put c (try-find-ce prog)))))
  (define timeout-thread (thread (λ () (sleep timeout) (channel-put c 'timeout))))
  (define (kill-all)
    (kill-thread verify-thread)
    (kill-thread ce-thread)
    (kill-thread timeout-thread))
  (match (channel-get c)
    [(and err (or (cons 'blame _) (cons (cons 'blame _) _)))
     ;; Wait for (maybe) counterexample, unless timeout
     (match (channel-get c)
       ['timeout (kill-all) err]
       [res (kill-all) res])]
    [result (kill-all) result]))

(: try-verify : .prog → Ve-Result)
;; Run verification on program
(define (try-verify p)
  (with-handlers ([exn:fail? (λ ([e : exn]) e)])
    (define ςs (verify p))
    ;;(printf "`try-verify` gives:~n~a~n" ςs)
    (for/list : (Listof Err-Result) ([ς ςs] #:when (match? ς (.ς (? .blm?) _ _)))
      (match-define (.ς (.blm l⁺ lᵒ v c) σ _) ς)
      (list 'blame l⁺ lᵒ (show-V σ v) (show-V σ c)))))

(: try-find-ce : .prog → Ce-Result)
;; Run counterexample on program
(define (try-find-ce p)
  (with-handlers ([exn:fail? (λ ([e : exn]) e)])
    #;(printf "CE read~n")
    (define ans (find-error p))
    ;;(printf "`try-find-ce` gives:~n~a~n" ans)
    (match ans
      [#f #;(printf "CE says safe~n") 'safe]
      [(cons σ^ (.blm l⁺ lᵒ v c))
        #;(printf "CE says CE~n")
       (match (model p σ^)
         [#f (list 'blame l⁺ lᵒ (show-V σ^ v) (show-V σ^ c))]
         [(? .σ? σ) (list 'ce (list 'blame l⁺ lᵒ (show-V σ v) (show-V σ c))
                          (show-ce p σ))])])))

(: raise-contract-error ([Any Any Any Any] [Any] . ->* . Void))
(define (raise-contract-error l⁺ lᵒ v c [ce #f])
  (define sure? #t)
  (define parties
    (cond [(equal? l⁺ lᵒ) (format "'~a' violates its own contract." l⁺)]
          [(equal? lᵒ 'Λ) (format "'~a' violates a contract in an application." l⁺)]
          [else (format "'~a' violates '~a'." l⁺ lᵒ)]))
  (define reason : String
    (match* (v c)
      [(_ `(arity=/c ,_)) "Wrong arity"]
      [(_ _)
       (match (replace-struct● v)
         [(and v `(begin (struct ,_ ()) ... ,_))
          (format "Value produced by~n ~a~nviolates predicate~n ~a"
                  (pretty v)
                  (pretty (replace-struct● c)))]
         [`(• ,cs ...)
          (set! sure? #f)
          (format "~a~n~a~nviolates predicate~n ~a"
                  (match (length cs)
                    [0 "Arbitrary value"]
                    [1 "Value contrained by contract"]
                    [_ "Value contrained by contracts"])
                  (string-join (for/list : (Listof String) ([c cs]) (format " ~a" (pretty c))) "\n")
                  (pretty (replace-struct● c)))]
         [_
          (format "Value~n ~a~nviolates predicate~n ~a"
                  (pretty v)
                  (pretty (replace-struct● c)))])]))
  (define ce-prog
    (cond [ce (format "An example module that breaks it:~n ~a"
                      (pretty `(module user racket
                                (require (submod "\"..\"" ,l⁺))
                                ,(replace-struct● ce))))]
          [else ""]))
  (error (format "~a: ~a~n~a~n~a~n"
                 (if sure? "Contract violation" "Possible contract violation")
                 parties
                 reason
                 ce-prog)))

(: replace-struct● : Any → Any)
;; Traverse the S-exp, replace all (struct• _) and insert top-level struct definitions
(define (replace-struct● e)

  (define-set new-names : Symbol)
  
  (define e′
    (let go! : Any ([e : Any e])
      (match e
        [`(● ,tag)
         (define name (string->symbol (format "s~a" (n-sub (assert tag exact-integer?)))))
         (new-names-add! name)
         `(,name)]
        [(list xs ...) (map go! xs)]
        [_ e])))
  
  (-begin
   `(,@(for/list : (Listof Any) ([name (in-set new-names)])
         `(struct ,name ()))
     ,e′)))
