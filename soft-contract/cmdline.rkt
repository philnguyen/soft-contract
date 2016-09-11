#lang typed/racket/base

(require racket/match
         racket/set
         racket/cmdline
         (except-in racket/list remove-duplicates)
         racket/pretty
         "utils/main.rkt"
         "ast/definition.rkt"
         "parse/main.rkt"
         "runtime/definition.rkt"
         (only-in "reduction/quick-step.rkt" run-file havoc-file)
         (only-in "proof-relation/ext.rkt" Timeout))

(Mode . ::= . 'light 'havoc 'expand)
(define mode : Mode 'havoc)
(define timeout : Nonnegative-Fixnum (Timeout))

(define fname
  (cast
   (command-line
    #:program "raco soft-contract"
    
    #:once-each
    [("-r" "--light")
     "Run program abstractly without havoc-ing each export"
     (set! mode 'light)]
    [("-e" "--expand")
     "Print expanded program (just for debugging, might look cryptic)"
     (set! mode 'expand)]

    #:args (fname) ; TODO re-enable file list
    fname)
   Path-String))

(: show-Vs : (Listof -V) → Sexp)
(define (show-Vs Vs)
  (match Vs
    [(list V) (show-V V)]
    [_ `(values ,@(map show-V Vs))]))

(: show-a : -ΓA → Sexp)
(define (show-a a)
  (match a
    [(-ΓA _ (-W Vs _)) (show-Vs Vs)]
    [(-ΓA _ (-blm l+ lo Cs Vs))
     `(blame ,l+ ,lo (contract: ,(show-Vs Cs)) (value: ,(show-Vs Vs)))]))

(parameterize ([Timeout timeout])
  (case mode
    [(expand)
     (define m (file->module fname))
     (pretty-write (show-module m))]
    [(light)
     (define-values (ans Σ) (run-file fname))
     (cond
       [(set-empty? ans)
        (printf "Safe~n")]
       [else
        (for ([A ans])
          (pretty-write (show-a A)))])]
    [(havoc)
     (define-values (ans Σ) (havoc-file fname))
     (define safe? : Boolean #t)
     (for ([A ans] #:when (-blm? (-ΓA-ans A)))
       (set! safe? #f)
       (pretty-write (show-a A)))
     (when safe?
       (printf "Safe~n"))]))
