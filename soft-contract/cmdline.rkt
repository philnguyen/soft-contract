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
         (only-in "run.rkt" run-file run-files havoc-file havoc-files)
         "settings.rkt")

(Mode . ::= . 'light 'havoc 'expand)
(define mode : Mode 'havoc)

(define fnames
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
    [("-p" "--progress")
     "Print progress"
     (debug-iter? #t)]
    [("-v" "--verbose")
     "Print debugging information"
     (debug-iter? #t)
     (debug-trace? #t)]

    #:args fnames ; TODO re-enable file list
    fnames)
   (Listof Path-String)))

(: show-Vs : (Listof (U -V -v)) → Sexp)
(define (show-Vs Vs)
  (match Vs
    [(list V) (show-blm-reason V)]
    [_ `(values ,@(map show-blm-reason Vs))]))

(: show-a : -ΓA → Sexp)
(define (show-a a)
  (match a
    [(-ΓA _ (-W Vs _)) (show-Vs Vs)]
    [(-ΓA _ (-blm l+ lo Cs Vs ℓ))
     `(blame ,l+ ,lo ,(map show-blm-reason Cs) ,(show-Vs Vs) (line ,(ℓ-line ℓ) col ,(ℓ-col ℓ)))]))

(case mode
  [(expand)
   (for ([m (in-list (map file->module fnames))])
     (pretty-write (show-module m))
     (printf "~n"))]
  [(light)
   (define-values (ans Σ) (run-files fnames))
   (cond
     [(set-empty? ans)
      (printf "Safe~n")]
     [else
      (for ([A ans])
        (pretty-write (show-a A)))])]
  [(havoc)
   (define-values (ans Σ) (havoc-files fnames))
   (define safe? : Boolean #t)
   (for ([A ans] #:when (-blm? (-ΓA-ans A)))
     (set! safe? #f)
     (pretty-write (show-a A)))
   (when safe?
     (printf "Safe~n"))])
