#lang typed/racket/base

(require racket/match
         (except-in racket/set for/set for*/set for/seteq for*/seteq)
         racket/cmdline
         racket/list
         racket/pretty
         racket/string
         bnf
         set-extras
         "utils/main.rkt"
         "ast/signatures.rkt"
         "runtime/signatures.rkt"
         "parse/signatures.rkt"
         "main.rkt")

(Mode . ::= . 'light 'havoc 'expand 'havoc-last 'havoc/profile)
(define mode : Mode 'havoc)

(define fnames
  (cast
   [command-line
    #:program "raco scv"
    
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
     "Dump progress"
     (db:iter? #t)]
    [("-d" "--profile")
     "Havoc with profiling"
     (set! mode 'havoc/profile)]
    [("-s" "--max-steps") n
     "Set maximum steps to explore"
     (db:max-steps (assert (string->number (assert n string?)) index?))]

    #:args (first-module . other-modules) ; TODO re-enable file list
    (cons first-module other-modules)]
   (Listof Path-String)))

(: main : (Listof Path-String) → Any)
(define (main fnames)

  (: run-with : ((Listof Path-String) → (Values (℘ Err) $)) (Listof Path-String) → Void)
  (define (run-with f files)
    (define-values (blms _) (f files))
    (print-blames blms))

  (: go : (Listof Path-String) → Any)
  (define (go fnames)
    (with-handlers ([exn:missing?
                     (match-lambda
                       [(exn:missing _ _ src id)
                        (define src* (canonicalize-path src))
                        (printf "- dependency: ~a for `~a`~n" src* id)
                        (assert (not (member src* fnames)))
                        (go (cons src* fnames))])])
      (case mode
        [(expand)
         (for ([m (in-list (parse-files fnames))])
           (pretty-write (show-module m))
           (printf "~n"))]
        [(light) (run-with run fnames)]
        [(havoc) (run-with havoc fnames)]
        [(havoc/profile) (run-with havoc/profile fnames)]
        [(havoc-last) (run-with havoc-last fnames)])))

  (go (map canonicalize-path fnames)))

(main fnames)
