#lang typed/racket/base
(provide feedback)
(require racket/match racket/list racket/port racket/string racket/pretty
         (only-in "utils.rkt" match?)
         (only-in "lang.rkt" .p)
         (only-in "verify/machine.rkt" .ς [e verify])
         (only-in "verify/closure.rkt" .blm?)
         (only-in "terify/machine.rkt" [ev find-error])
         (only-in "terify/provability.rkt" [model model/untyped])
         (only-in "terify/query-z3.rkt" [model model/z3])
         (only-in "terify/show.rkt" show-ce show-A)
         (only-in "terify/closure.rkt" .σ?))
(require/typed "terify/read.rkt"
  [(read-p read/ce) (Sexp → .p)])

(define-type Result (U 'timeout Ce-Result Ve-Result))
(define-type Ce-Result (U 'safe (List 'ce (Option (List Any Any)))))
(define-type Ve-Result (U 'safe (List 'error Any)))

(: feedback ([Sexp] [Integer] . ->* . Any))
(define (feedback prog [timeout 30])
  (match (run prog timeout)
    ['timeout (printf "Timeout after ~a seconds~n" timeout)]
    ['safe (printf "Program is safe")]
    [`(error (blame ,who ,whom ,what ,why))
     (raise-contract-error who whom what why)]
    [`(ce #f) ; FIXME
     (error "Contract violation")]
    [`(ce ((blame ,who ,whom ,what ,why) ,ce))
     (raise-contract-error who whom what why ce)]))

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
  (define p (read/ce prog))
  #;(printf "CE read~n")
  (match (find-error p)
    [#f #;(printf "CE says safe~n") 'safe]
    [(cons σ^ blm)
     #;(printf "CE says CE~n")
     (list 'ce
           (match (model/z3 (model/untyped p σ^))
             [#f #;(printf "CE can't find~n") #f]
             [(? .σ? σ) #;(printf "CE finds~n") (list (show-A σ blm) (show-ce p σ))]))]))

(: raise-contract-error ([Any Any Any Any] [Any] . ->* . Any))
(define (raise-contract-error who whom what why [ce #f])
  ;; FIXME shameless code dup
  (cond
   [(equal? who whom)
    (cond
     [ce
      (error
       '|Contract violation|
       "'~a' violates its own contract:~n Value:~n  ~a~n violates predicate~n  ~a~nAn example program that breaks it:~n ~a"
       who (pretty what) (pretty why) (pretty ce))]
     [else
      (error '|Contract violation|
             "'~a' violates its own contract:~n Value:~n  ~a~n violates predicate~n  ~a."
             who (pretty what) (pretty why))])]
   [else
    (cond
     [ce
      (error
       '|Contract violation|
       "'~a' violates '~a':~n Value:~n  ~a~n violates predicate~n  ~a~nAn example program that breaks it:~n ~a"
       who whom (pretty what) (pretty why) (pretty ce))]
     [else
      (error
       '|Contract violation|
       "'~a' violates '~a':~n Value:~n  ~a~n violates predicate~n  ~a."
       who whom (pretty what) (pretty why))])]))

(: pretty : Any → String)
(define (pretty x)
  (parameterize ([pretty-print-columns 80])
    (string-trim (with-output-to-string (λ () (pretty-display x))))))
