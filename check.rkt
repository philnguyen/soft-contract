#lang typed/racket/base
(provide feedback)
(require racket/match racket/list racket/port racket/string racket/set
         (only-in "query-z3.rkt" total-z3-time reset-z3-time!)
         (only-in "utils.rkt" match? pretty n-sub define-set)
         (only-in "lang.rkt" .p)
         (only-in "verify/machine.rkt" .ς [e verify])
         (only-in "runtime.rkt" .blm? .blm .σ .σ?)
         (only-in "show.rkt" show-V show-A show-ce)
         (only-in "ce/machine.rkt" [ev find-error])
         (only-in "ce/model.rkt" model))
(require/typed "ce/read.rkt"
  [(read-p read/ce) (Sexp → .p)])
(require/typed "read.rkt"
  [-begin ((Listof Any) → Any)])

(: feedback ([Sexp] [Integer] . ->* . Any))
(define (feedback prog [timeout 30])
  (log-info "feedback ... ~a" (current-process-milliseconds))
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
(define-type Err-Result (List 'blame Symbol Symbol Any Any))

(: run : Sexp Integer → Result)
;; Verify + Seek counterexamples at the same time, whichever finishes first
(define (run prog timeout)
  (log-info "Starting run ... ~a" (current-process-milliseconds))
  (reset-z3-time!)
  (define c : (Channelof Result) (make-channel))
  (define verify-thread (thread (λ () (channel-put c (try-verify prog)))))
  (define ce-thread (thread (λ () (channel-put c (try-find-ce prog)))))
  (define timeout-thread (thread (λ () (sleep timeout) (channel-put c 'timeout))))
  (define (kill-all)
    (kill-thread verify-thread)
    (kill-thread ce-thread)
    (kill-thread timeout-thread)
    (log-info "Killed threads ... ~a" (current-process-milliseconds)))
  (log-info "Spawned threads ... ~a" (current-process-milliseconds))
  (match (channel-get c)
    [(and err (or (cons 'blame _) (cons (cons 'blame _) _)))
     (log-info "Got an error ... ~a (z3 time: ~a)" (current-process-milliseconds) total-z3-time)
     ;; Wait for (maybe) counterexample, unless timeout
     (match (channel-get c)
       ['timeout (kill-all) err]
       [res (kill-all) res])]
    [result 
     (log-info "Got a result ... ~a  (z3 time: ~a)" (current-process-milliseconds) total-z3-time)
     (kill-all) result]))

(: try-verify : Sexp → Ve-Result)
;; Run verification on program
(define (try-verify prog)
  (with-handlers ([exn:fail? (λ ([e : exn]) e)])
    (define ςs (verify prog))
    (for/list : (Listof Err-Result) ([ς ςs] #:when (match? ς (.ς (? .blm?) _ _)))
      (match-define (.ς (.blm l⁺ lᵒ v c) σ _) ς)
      (list 'blame l⁺ lᵒ (show-V σ v) (show-V σ c)))))

(: try-find-ce : Sexp → Ce-Result)
;; Run counterexample on program
(define (try-find-ce prog)
  (with-handlers ([exn:fail? (λ ([e : exn]) e)])
    (define p (read/ce prog))
    #;(printf "CE read~n")
    (match (find-error p)
      [#f #;(printf "CE says safe~n") 'safe]
       [(cons σ^ (.blm l⁺ lᵒ v c))
        #;(printf "CE says CE~n")
        (match (model p σ^)
          [#f (list 'blame l⁺ lᵒ (show-V σ^ v) (show-V σ^ c))]
          [(? .σ? σ) (list 'ce (list 'blame l⁺ lᵒ (show-V σ v) (show-V σ c))
                           (second #|for now|# (show-ce p σ)))])])))

(: raise-contract-error ([Any Any Any Any] [Any] . ->* . Any))
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

(: new-name! : Any → Symbol)
;; Generate a fresh struct name for each new tag
(define new-name!
  (let ([count 0]
        [m : (HashTable Any Symbol) (make-hash)])
    (λ (tag)
      (hash-ref! m tag
                 (λ ()
                   (begin0 (string->symbol (format "s~a" (n-sub count)))
                     (set! count (+ 1 count))))))))

(: replace-struct● : Any → Any)
;; Traverse the S-exp, replace all (struct• _) and insert top-level struct definitions
(define (replace-struct● e)

  (define-set new-names : Symbol)
  
  (define e′
    (let go! : Any ([e : Any e])
      (match e
        [`(struct● ,tag)
         (define name (new-name! tag))
         (new-names-add! name)
         `(,name)]
        [(list xs ...) (map go! xs)]
        [_ e])))
  
  (-begin
   `(,@(for/list : (Listof Any) ([name (in-set new-names)])
         `(struct ,name ()))
     ,e′)))
