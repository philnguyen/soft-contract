#lang typed/racket/base

(require racket/match
         racket/set
         racket/cmdline
         racket/list
         racket/pretty
         "utils/main.rkt"
         "ast/main.rkt"
         "parse/main.rkt"
         "runtime/definition.rkt"
         (only-in "run.rkt" run-file havoc-file)
         (only-in "reduction/quick-step.rkt" debug?)
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
    [("-v" "--verbose")
     "Print debugging information"
     (debug? #t)]

    #:args (fname) ; TODO re-enable file list
    fname)
   Path-String))

(: show-Vs : (Listof (U -V -v)) → Sexp)
(define (show-Vs Vs)
  (match Vs
    [(list V) (show-V-or-v V)]
    [_ `(values ,@(map show-V-or-v Vs))]))

(: show-a : -ΓA → Sexp)
(define (show-a a)
  (match a
    [(-ΓA _ (-W Vs _)) (show-Vs Vs)]
    [(-ΓA _ (-blm l+ lo Cs Vs ℓ))
     `(blame ,l+ ,lo ,(show-Vs Cs) ,(show-Vs Vs) ,(show-ℓ ℓ))]))

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
