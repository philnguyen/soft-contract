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
    [("-o" "--optimize")
     "Dump optimized programs after verification"
     (opt? #t)]
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

(: main : (Listof Path-String) → Any)
(define (main fnames)

  (Summary . ≜ . (Immutable-HashTable ℓ (Listof (℘ (U T V)))))

  (: ⊕ : (℘ (U T V)) T^ → (℘ (U T V)))
  (define (⊕ vals val) (if (set? val) (∪ vals val) (set-add vals val)))
  (define (val->string [v : (U T V)]) (format "~a" (show-T v)))
  (define (show-val-set [vs : (℘ (U V T))])
    (if (= 1 (set-count vs))
        (val->string (set-first vs))
        (string-join (set-map vs val->string) " " #:before-first "{" #:after-last "}")))

  (: run-with : ((Listof Path-String) → (Values (℘ Blm) Σ)) (Listof Path-String) → Void)
  (define (run-with f files)
    (define-values (blms* _) (f files))
    (define blms
      (for/fold ([acc : Summary (hash)]) ([b (in-set blms*)])
        (match b
          [(Blm _ ℓ _ (list Cs) (cons fun args))
           #:when (if (set? Cs)
                      (∋ Cs 'size-change-terminating/c)
                      (eq? Cs 'size-change-terminating/c))
           (hash-update
            acc ℓ
            (λ ([vals : (Listof (℘ (U T V)))]) (map ⊕ vals (cons fun args)))
            (λ () (make-list (+ 1 (length args)) ∅)))]
          [_ acc])))
    (print-blames blms))

  (: print-blame : ℓ (℘ (U T V)) (Listof (℘ (U T V))) String → Void)
  (define (print-blame ℓ fun args idx)

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

    (printf "~a ~a:~a:~a~n" idx (ℓ-src ℓ) (ℓ-line ℓ) (ℓ-col ℓ))
    (printf "    - Function: ~a~n" (show-val-set fun))
    (printf "    - Arguments:~n")
    (for ([arg (in-list args)])
      (printf "        * ~a~n" (show-val-set arg))))

  (: print-blames : Summary → Void)
  (define (print-blames summary)
    (define maybe-plural (match-lambda [1 ""] [_ "s"]))
    (match (hash-count summary)
      [0 (printf "Safe~n")]
      [n
       (printf "Found ~a possible SCT violation~a~n" n (maybe-plural n))
       (for ([(ℓ vals) (in-hash summary)] [i (in-naturals)])
         (print-blame ℓ (car vals) (cdr vals) (format "(~a)" (+ 1 i))))]))

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
        [(havoc-last) (run-with havoc-last fnames)]
        [(debug) (void (viz fnames))])))

  (go (map canonicalize-path fnames)))

(main fnames)
