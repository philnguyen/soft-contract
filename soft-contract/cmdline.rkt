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

(Mode . ::= . 'light 'havoc 'expand 'havoc-last 'debug 'debug-cg)
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
    [("-d" "--debug")
     "Show graph"
     (set! mode 'debug)]
    [("-c" "--debug-call-graph")
     "Show call graph"
     (set! mode 'debug-cg)]
    [("-s" "--max-steps") n
     "Set maximum steps to explore"
     (db:max-steps (assert (string->number (assert n string?)) exact-nonnegative-integer?))]

    #:args (first-module . other-modules) ; TODO re-enable file list
    (cons first-module other-modules)]
   (Listof Path-String)))

(: main : (Listof Path-String) → Void)
(define (main fnames)

  (: run-with : ((Listof Path-String) → (Values (℘ Blm) Σ)) (Listof Path-String) → Void)
  (define (run-with f files)
    (define-values (blms _) (f files))
    (print-blames blms))

  (: print-blame : Blm String → Void)
  (define (print-blame blm idx)

    (: show-set (∀ (X) (X → Sexp) X → String))
    (define (show-set f x)
      (define s (f x))
      (cond [(and (set? x) (list? s))
             (if (= 1 (set-count x))
                 (format "~a" (car s))
                 (string-join (map (λ (x) (format "~a" x)) s)
                              #:before-first "{"
                              #:after-last "}"))]
            [else (format "~a" s)]))
    
    (match-define (Blm ℓ lo Cs Vs) blm)
    (printf "~a ~a:~a:~a~n" idx (ℓ-src ℓ) (ℓ-line ℓ) (ℓ-col ℓ))
    (printf "    - Contract from: ~a~n" lo)
    (printf "    - Expected: ~a~n"
            (match Cs
              [(list C) (show-set show-blm-reason C)]
              ['() "no value"]
              [_ (format "~a values: ~a" (length Cs) (map show-blm-reason Cs))]))
    (printf "    - Given: ~a~n"
            (match Vs
              [(list V) (show-set show-V^ V)]
              ['() "(values)"]
              [_ (format "~a values: ~a" (length Vs) (map show-V^ Vs))])))

  (: print-blames : (℘ Blm) → Void)
  (define (print-blames blames) 
    (match (set-count blames)
      [0 (printf "Safe~n")]
      [1 (printf "Found 1 possible contract violation:~n")
         (print-blame (set-first blames) "")]
      [n
       (printf "Found ~a possible contract violations~n" n)
       (for ([blm (in-set blames)]
             [i (in-naturals)])
         (print-blame blm (format "(~a)" i)))]))

  (: go : (Listof Path-String) → Void)
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
        [(havoc-last) (run-with havoc-last fnames)]
        [(debug) (void (viz fnames))]
        [(debug-cg) (viz-call-graph fnames)])))

  (go (map canonicalize-path fnames)))

(main fnames)
