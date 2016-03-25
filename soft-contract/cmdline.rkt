#lang typed/racket/base

(require racket/match
         racket/set
         racket/cmdline
         (except-in racket/list remove-duplicates)
         racket/pretty
         ;(only-in "check.rkt" analyze)
         "utils/main.rkt"
         "ast/definition.rkt"
         "parse/main.rkt"
         "runtime/definition.rkt"
         (only-in "reduction/main.rkt" run-files havoc-files))

(Mode . ::= . 'light 'havoc 'expand)
(define mode : Mode 'havoc)

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

(: show-a : -A → Sexp)
(define (show-a a)
  (match a
    [(-ΓW _ (-W Vs _)) (show-Vs Vs)]
    [(-ΓE _ (-blm l+ lo Cs Vs))
     `(blame ,l+ ,lo (contract: (show-Vs Cs)) (value: (show-Vs Vs)))]))

(case mode
  [(expand)
   (match-define (list m) (files->modules (list fname)))
   (pretty-write (show-module m))]
  [(light)
   (define-values (ans M Ξ) (run-files fname))
   (for ([A ans])
     (pretty-write (show-a A)))]
  [(havoc)
   (define-values (ans M Ξ) (havoc-files fname))
   (for ([A ans])
     (pretty-write (show-a A)))])
