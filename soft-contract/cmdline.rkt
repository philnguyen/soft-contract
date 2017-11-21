#lang typed/racket/base

(require racket/match
         racket/set
         racket/cmdline
         racket/list
         racket/pretty
         bnf
         set-extras
         "utils/main.rkt"
         "ast/signatures.rkt"
         "runtime/signatures.rkt"
         "parse/signatures.rkt"
         "main.rkt")

(Mode . ::= . 'light 'havoc 'expand 'havoc-last)
(define mode : Mode 'havoc)

(define (print-result [ans : (℘ -A)])
  (define safe? : Boolean #t)
  (for ([A ans] #:when (-blm? A))
    (set! safe? #f)
    (pretty-write (show-a A)))
  (when safe?
    (printf "Safe~n")))

(define fnames
  (cast
   (command-line
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
     "Print progress"
     (debug-iter? #t)]
    [("-v" "--verbose")
     "Print debugging information"
     (debug-iter? #t)
     (debug-trace? #t)]
    [("-s" "--max-steps") n
     "Set maximum steps to explore"
     (max-steps (assert (string->number (assert n string?)) exact-nonnegative-integer?))]

    #:args (first-module . other-modules) ; TODO re-enable file list
    (cons first-module other-modules))
   (Listof Path-String)))

(: show-a : -A → Sexp)
(define (show-a a)
  (match a
    [(list V) (show-V^ V)]
    [(? list? Vs) `(values ,@(map show-V^ Vs))]
    [(-blm l+ lo Cs Vs ℓ)
     `(blame
       [line ,(ℓ-line ℓ) col ,(ℓ-col ℓ)]
       [violator : ,l+]
       [contract from : ,lo]
       [contracts : ,@(map show-blm-reason Cs)]
       [values : ,@(map show-V^ Vs)])]))

(: main : (Listof Path-String) → Void)
(define (main fnames)

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
         (define-values (ans _) (havoc-last-file fnames))
         (print-result ans)])))

  (go (map canonicalize-path fnames)))

(main fnames)
