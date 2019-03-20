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
(define opt? ((inst make-parameter Boolean) #f))

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
    [("-o" "--optimize")
     "Dump optimized programs after verification"
     (opt? #t)]
    [("-s" "--max-steps") n
     "Set maximum steps to explore"
     (db:max-steps (assert (string->number (assert n string?)) index?))]

    #:args (first-module . other-modules) ; TODO re-enable file list
    (cons first-module other-modules)]
   (Listof Path-String)))

(: main : (Listof Path-String) → Any)
(define (main fnames)

  (: run-with : ((Listof Path-String) → (Values (℘ Err) $)) (Listof Path-String) → (℘ Err))
  (define (run-with f files)
    (define-values (blms _) (f files))
    (print-blames blms)
    blms)

  (: print-blame : Err String → Void)
  (define (print-blame blm idx)
    (match blm
      [(Blm l+ ℓ:site ℓ:origin Cs Vs)
       (printf "~a At: ~a~n" idx (show-full-ℓ ℓ:site))
       (printf "    - Blaming: ~a~n" l+)
       (printf "    - Contract from: ~a ~n" (show-full-ℓ ℓ:origin))
       (printf "    - Expected: ~a~n"
               (match Cs
                 [(list C) (show-V^ C)]
                 ['() "no value"]
                 [_ (format "~a values: ~a" (length Cs) (show-W Cs))]))
       (printf "    - Given: ~a~n"
               (match Vs
                 [(list V) (show-V^ V)]
                 ['() "(values)"]
                 [_ (format "~a values: ~a" (length Vs) (show-W Vs))]))]
      [(Err:Raised s ℓ)
       (printf "~a Error: ~a~n" idx s)
       (printf "    - At: ~a~n" (show-full-ℓ ℓ))]
      [(Err:Undefined x ℓ)
       (printf "~a Undefined `~a`~n" idx x)
       (printf "    - At: ~a~n" (show-full-ℓ ℓ))]
      [(Err:Values n E W ℓ)
       (printf "~a Expected ~a values, given ~a:~n" idx n (length W))
       (for ([Vs (in-list W)])
         (printf "    - ~a~n" (show-V^ Vs)))
       (printf "    - At: ~a~n" (show-full-ℓ ℓ))]
      [(Err:Arity f xs ℓ)
       (printf "~a Function applied with wrong arity~n" idx)
       (if (V? f)
           (printf "    - Function: ~a~n" (show-V f))
           (printf "    - Function defined at ~a~n" (show-full-ℓ f)))
       (if (integer? xs)
           (printf "    - Given ~a arguments~n" xs)
           (begin
             (printf "    - Given ~a arguments:~n" (length xs))
             (for ([Vs (in-list xs)])
               (printf "        + ~a~n" (show-V^ Vs)))))
       (printf "    - At: ~a~n" (show-full-ℓ ℓ))]
      [(Err:Varargs W₀ Vᵣ ℓ)
       (printf "~a Invalid number of rest args~n" idx)
       (printf "    - ~a inits:~n" (length W₀))
       (for ([V (in-list W₀)])
         (printf "        * ~a~n" (show-V^ V)))
       (printf "    - rest: ~a~n" (show-V^ Vᵣ))
       (printf "    - Application at ~a~n" (show-full-ℓ ℓ))]
      [(Err:Sealed x ℓ)
       (printf "~a Attempt to inspect value sealed in ~a~n" idx x)
       (printf "    - At: ~a~n" (show-full-ℓ ℓ))]))

  (: print-blames : (℘ Err) → Void)
  (define (print-blames blames)
    (define maybe-plural (match-lambda [1 ""] [_ "s"]))
    (match (set-count blames)
      [0 (printf "Safe~n")]
      [n
       (printf "Found ~a possible error~a~n" n (maybe-plural n))
       (for ([b (in-set blames)] [i (in-naturals)])
         (print-blame b (format "(~a)" (+ 1 i))))]))

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
        [(havoc) (define blms (run-with havoc fnames))
                 (when (opt?)
                   (printf "~nOptimized modules:~n")
                   (for ([m (in-list (parse-files fnames))])
                     (pretty-write (show-module (optimize m blms)))
                     (printf "~n")))]
        [(havoc/profile)
         (define blms (run-with havoc/profile fnames))
         (when (opt?)
           (printf "~nOptimized modules:~n")
           (for ([m (in-list (parse-files fnames))])
             (pretty-write (show-module (optimize m blms)))
             (printf "~n")))]
        [(havoc-last) (run-with havoc-last fnames)])))

  (go (map canonicalize-path fnames)))

(main fnames)
