#lang typed/racket/base
(provide feedback)
(require racket/match racket/list racket/port racket/string
         (only-in "utils.rkt" match? pretty)
         (only-in "lang.rkt" .p)
         (only-in "verify/machine.rkt" .ς [e verify])
         (prefix-in ve: (only-in "verify/runtime.rkt" .blm? .blm .σ .σ?))
         (prefix-in ve: (only-in "verify/show.rkt" show-V))
         (only-in "terify/machine.rkt" [ev find-error])
         (only-in "terify/provability.rkt" [model model/untyped])
         (only-in "terify/model.rkt" [model model/z3])
         (prefix-in ce: (only-in "terify/show.rkt" show-ce show-A show-V))
         (prefix-in ce: (only-in "terify/runtime.rkt" .blm? .blm .σ .σ?)))
(require/typed "terify/read.rkt"
  [(read-p read/ce) (Sexp → .p)])

(: feedback ([Sexp] [Integer] . ->* . Any))
(define (feedback prog [timeout 30])
  (match (run prog timeout)
    ['timeout (printf "Timeout after ~a seconds~n" timeout)]
    [(or 'safe (list)) (printf "Program is safe")]
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
(define-type Ce-Result (U 'safe Err-Result (List 'ce Err-Result Any)))
(define-type Ve-Result (Listof Err-Result))
(define-type Err-Result (U (List 'blame Symbol Symbol Any Any) exn))

(: run : Sexp Integer → Result)
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

(: try-verify : Sexp → Ve-Result)
;; Run verification on program
(define (try-verify prog)
  (with-handlers ([exn:fail? (λ (e) e)])
    (define ςs (verify prog))
    (for/list : (Listof Err-Result) ([ς ςs] #:when (match? ς (.ς (? ve:.blm?) _ _)))
      (match-define (.ς (ve:.blm l⁺ lᵒ v c) σ _) ς)
      (list 'blame l⁺ lᵒ (ve:show-V σ v) (ve:show-V σ c)))))

(: try-find-ce : Sexp → Ce-Result)
;; Run counterexample on program
(define (try-find-ce prog)
  (with-handlers ([exn:fail? (λ (e) e)])
    (define p (read/ce prog))
    #;(printf "CE read~n")
    (match (find-error p)
      [#f #;(printf "CE says safe~n") 'safe]
       [(cons σ^ (ce:.blm l⁺ lᵒ v c))
        #;(printf "CE says CE~n")
        (match (model/z3 (model/untyped p σ^))
          [#f (list 'blame l⁺ lᵒ (ce:show-V σ^ v) (ce:show-V σ^ c))]
          [(? ce:.σ? σ) (list 'ce (list 'blame l⁺ lᵒ (ce:show-V σ v) (ce:show-V σ c))
                              (second #|for now|# (ce:show-ce p σ)))])])))

(: raise-contract-error ([Any Any Any Any] [Any] . ->* . Any))
(define (raise-contract-error l⁺ lᵒ v c [ce #f])
  (define parties
    (cond [(equal? l⁺ lᵒ) (format "'~a' violates its own contract." l⁺)]
          [(equal? lᵒ 'Λ) (format "'~a' violates a contract in an application." l⁺)]
          [else (format "'~a' violates '~a'." l⁺ lᵒ)]))
  (define reason
    (match* (v c)
      [(_ `(arity=/c ,_)) "Wrong arity"]
      [(_ _) (format "Value~n ~a~nviolates predicate~n ~a" (pretty v) (pretty c))]))
  (define ce-prog
    (cond [ce (format "An example module that breaks it:~n ~a"
                      (pretty `(module user racket
                                (require ,l⁺)
                                ,ce)))]
          [else ""]))
  (error (format "Contract violation: ~a~n~a~n~a~n" parties reason ce-prog)))
