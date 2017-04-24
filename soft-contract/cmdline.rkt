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

(Mode . ::= . 'light 'havoc 'expand 'havoc-last)
(define mode : Mode 'havoc)

(define fnames
  (cast
   (command-line
    #:program "raco soft-contract"
    
    #:once-each
    [("-l" "--last-only")
     "Only havoc the last module in argument list"
     (set! mode 'havoc-last)]
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
     `(blame
       [line ,(ℓ-line ℓ) col ,(ℓ-col ℓ)]
       [violator : ,l+]
       [contract from : ,lo]
       [contracts : ,@(map show-blm-reason Cs)]
       [values : ,@(map show-V Vs)])]))

(case mode
  [(expand)
   (for ([m (in-list (parse-files fnames))])
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
   (define-values (ans _) (havoc-files fnames))
   (print-result ans)]
  [(havoc-last)
   (define-values (ans _) (havoc-last fnames))
   (print-result ans)])

(define (print-result [ans : (℘ -ΓA)])
  (define safe? : Boolean #t)
  (for ([A ans] #:when (-blm? (-ΓA-ans A)))
    (set! safe? #f)
    (pretty-write (show-a A)))
  (when safe?
    (printf "Safe~n")))
