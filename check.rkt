#lang typed/racket/base
(provide feedback)
(require racket/match racket/list
         (only-in "verify/machine.rkt" [e verify])
         (only-in "verify/machine.rkt" .ς)
         (only-in "verify/closure.rkt" .blm?)
         (only-in "terify/machine.rkt" [ev find-error])
         (only-in "terify/provability.rkt" [model model/untyped])
         (only-in "terify/query-z3.rkt" [model model/z3])
         (only-in "terify/show.rkt" show-ce show-A)
         (only-in "terify/closure.rkt" .σ?)
         (only-in "terify/lang.rkt" .p)
         (only-in "terify/utils.rkt" match?))
(require/typed "terify/read.rkt"
  [read-p (Sexp → .p)])

(define Timeout 5)
(define-type Result (U 'timeout Ce-Result Ve-Result))
(define-type Ce-Result (U 'safe (List 'ce (Option (List Any Any)))))
(define-type Ve-Result (U 'safe (List 'error Any)))

(: feedback : Sexp → Result)
;; Verify + Seek counterexamples at the same time, whichever finishes first
(define (feedback prog)
  (define c : (Channelof Result) (make-channel))
  (define verify-thread (thread (λ () (channel-put c (try-verify prog)))))
  (define ce-thread (thread (λ () (channel-put c (try-find-ce prog)))))
  (define timeout-thread (thread (λ () (sleep Timeout) (channel-put c 'timeout))))
  (define (kill-all)
    (kill-thread verify-thread)
    (kill-thread ce-thread)
    (kill-thread timeout-thread))
  (match (channel-get c)
    [(and err (list 'error Any))
     ;; Wait for (maybe) counterexample, unless timeout
     (match (channel-get c)
       ['timeout (kill-all) err]
       [res (kill-all) res])]
    [result (kill-all) result]))

(: try-verify : Sexp → Ve-Result)
;; Run verification on program
(define (try-verify prog)
  (define ςs (verify prog))
  (define errors
    (for/list : (Listof Any) ([ς ςs] #:when (match? ς (.ς (? .blm?) _ _)))
      ς))
  (match errors
    [(list) #;(printf "VE says safe~n") 'safe]
    [errors (list 'error (remove-duplicates errors))]))

(: try-find-ce : Sexp → Ce-Result)
;; Run counterexample on program
(define (try-find-ce prog)
  (define p (read-p prog))
  (match (find-error p)
    [#f #;(printf "CE says safe~n") 'safe]
    [(cons σ^ blm)
     (list 'ce
           (match (model/z3 (model/untyped p σ^))
             [#f #f]
             [(? .σ? σ) (list (show-A σ blm) (show-ce p σ))]))]))
