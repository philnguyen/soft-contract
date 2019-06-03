#lang typed/racket/base

(require racket/match
         racket/set
         racket/file
         racket/string
         racket/bool
         typed/rackunit
         set-extras
         "../utils/main.rkt"
         "../runtime/signatures.rkt"
         "../main.rkt")

(define TIMEOUT 1200)

(define elapsed ((inst make-parameter (Option Integer)) #f)) ; HACK to avoid passing around

(: run-handler (∀ (α) ((℘ Err) → α) (Listof Path-String) → α))
(define (run-handler f ps)
  (define t₀ (current-milliseconds)) ; can't use `time-apply`
  (match (length ps)
    [1 (printf "~a~n" (car ps))]
    [n (printf "~a files:~n" n)
       (for ([p (in-list ps)])
         (printf "  - ~a~n" p))])
  (define-values (es _) (havoc ps))
  (parameterize ([elapsed (- (current-milliseconds) t₀)])
    (f es)))

(: check : Any (Option Natural) (Option Natural) → (℘ Err) → Any)
(define ((check msg lo hi) errors)
  (define n (set-count errors))
  (if (and (implies lo (<= lo n)) (implies hi (<= n hi)))
      (printf "    ✓ ~a~a~n" msg (if (elapsed) (format " (~ams)" (elapsed)) ""))
      (fail
       (format "Expect numberof errors in range ⟨~a,~a⟩, got ~a" (or lo '-∞) (or hi '+∞) n))))

(define check-safe (check 'Safe 0 0))
(define check-fail (check 'Failed 1 #f))

(: test : (U Path-String (Listof Path-String)) ((℘ Err) → Any) → Any)
(define (test path f)
  (define (run-on-files [fns : (Listof Path-String)])
    (test-case (if (= 1 (length fns))
                   (car fns)
                   (format "~a files:" (length fns)))
      (with-handlers ([exn?
                       (λ ([e : exn])
                         (fail (format "Exception: ~a~n" (exn-message e))))])
        (unless (with-time-limit : Any TIMEOUT (run-handler f fns))
          (fail (format "Timeout after ~a seconds" TIMEOUT))))))

  (cond
    [(path-string? path)
     (define path* (format "programs/~a" path))
     (cond
       [(directory-exists? path*)
        (for* ([file-path (in-directory path*)]
               [fn (in-value (path->string file-path))]
               #:when (regexp-match-exact? #rx".*rkt" fn))
          (run-on-files (list fn)))]
       [else
        (run-on-files (list path*))])]
    [(list? path)
     (run-on-files path)]))

(module+ test
  
  ;; Order doesn't matter. I just run shorter ones first
  (test   "safe/octy" check-safe)
  (test "unsafe/octy" check-fail)

  #;(test "safe/issues/issue-103.rkt" check-safe)
  #;(test "unsafe/issues/issue-103.rkt" check-fail)

  ;; Mochi
  (test "safe/mochi/ack.rkt" check-safe)
  #;(test "safe/mochi/fhnhn.rkt" check-safe)
  (test "safe/mochi/fold-div.rkt" check-safe)
  (test "safe/mochi/fold-fun-list.rkt" check-safe)
  (test "safe/mochi/hors.rkt" check-safe)
  (test "safe/mochi/hrec.rkt" check-safe)
  (test "safe/mochi/intro1.rkt" check-safe)
  #;(test "safe/mochi/intro2.rkt" check-safe)
  #;(test "safe/mochi/intro3.rkt" check-safe)
  (test "safe/mochi/isnil.rkt" check-safe)
  #;(test "safe/mochi/l-zipmap.rkt" check-safe)
  #;(test "safe/mochi/l-zipunzip.rkt" check-safe)
  (test "safe/mochi/map-foldr.rkt" check-safe)
  (test "safe/mochi/mappend.rkt" check-safe)
  #;(test "safe/mochi/mult.rkt" check-safe)
  #;(test "safe/mochi/neg.rkt" check-safe)
  (test "safe/mochi/nth0.rkt" check-safe)
  (test "safe/mochi/r-file.rkt" check-safe)
  #;(test "safe/mochi/r-lock.rkt" check-safe)
  #;(test "safe/mochi/repeat.rkt" check-safe)
  #;(test "safe/mochi/reverse.rkt" check-safe)
  #;(test "safe/mochi/sum.rkt" check-safe)
  #;(test "safe/mochi/zip.rkt" check-safe)
  #;(test "safe/mochi/mem.rkt" check-safe)
  #;(test "safe/mochi/mc91.rkt" (check 'Ok-pos 0 1))

  (test   "safe/misc" check-safe)
  (test "unsafe/misc" check-fail)

  (test "paper/match.rkt" check-safe)
  (test "paper/match-no-check.rkt" check-safe)
  (test "paper/match-unsafe.rkt" check-fail)
  (test "paper/escape.rkt" check-safe)
  #;(test "paper/escape-safe.rkt" check-safe)
  (test "paper/escape-conservative.rkt" check-fail)
  (test "paper/factorial.rkt" check-safe)
  (test "paper/havoc-1.rkt" check-fail)
  #;(test "paper/havoc-2.rkt" check-fail) ; FIXME false-neg from unsound gc
  (test "paper/mutable-box-as-closure.rkt" check-safe)
  #;(test "paper/succ.rkt" check-safe)
  (test "paper/succ-incorrect.rkt" check-fail)

  (test   "safe/softy" check-safe)
  (test "unsafe/softy" check-fail)

  (test   "safe/termination/fo-sc" check-safe)
  (test "unsafe/termination/fo-sc" check-fail)
  (test "safe/termination/ho-sc/ack.rkt" (check 'Ok-pos 0 #f))
  (test "safe/termination/ho-sc/fg.rkt" check-safe)
  (test "safe/termination/ho-sc/fold.rkt" check-safe)
  (test "unsafe/termination/ho-sc" check-fail)
  (test "safe/termination/krauss/permute.rkt" check-safe)
  (test "safe/termination/manolios/fig-6.rkt" check-safe)
  (test "safe/termination/vazou/map.rkt" check-safe)
  (test "safe/termination/vazou/merge.rkt" check-safe)
  (test "safe/termination/vazou/tfact.rkt" check-safe)
  (test "unsafe/termination/krauss" check-fail)
  (test "unsafe/termination/manolios" check-fail)
  (test "unsafe/termination/vazou" check-fail)

  (test   "safe/proofs/inductive.rkt" check-safe)
  (test "unsafe/proofs/inductive.rkt" check-fail)

  (test "safe/issues/cons-of-list.rkt" check-safe)
  (test "safe/issues/list2vector.rkt" check-safe)
  (test "safe/issues/letrec-escape.rkt" check-safe)
  (test "safe/issues/oop-encoding.rkt" check-safe)
  (test "safe/issues/issue-62.rkt" check-safe)
  (test "safe/issues/issue-63.rkt" check-safe)
  (test "safe/issues/issue-64.rkt" check-safe)
  (test "safe/issues/issue-66.rkt" check-safe)
  (test "safe/issues/issue-67.rkt" check-safe)
  (test "safe/issues/issue-72.rkt" check-safe)
  (test "safe/issues/issue-73.rkt" check-safe)
  (test "safe/issues/issue-76.rkt" check-safe)
  (test "safe/issues/make-vector.rkt" check-safe)
  (test "safe/issues/ctc-var.rkt" check-safe)
  (test "safe/issues/issue-79.rkt" check-safe)
  (test "safe/issues/issue-61.rkt" check-safe)
  (test "safe/issues/issue-74.rkt" check-safe)
  (test "safe/issues/issue-80.rkt" check-safe)
  (test "safe/issues/issue-81.rkt" check-safe)
  (test '("programs/safe/issues/issue-65/main.rkt"
          "programs/safe/issues/issue-65/example.rkt")
        check-safe)
  (test "safe/issues/issue-82.rkt" check-safe)
  (test '("programs/safe/issues/issue-84/module1.rkt"
          "programs/safe/issues/issue-84/module2.rkt")
        check-safe)
  (test "safe/issues/issue-85.rkt" check-safe)
  (test '("programs/safe/issues/issue-87/foo.rkt"
          "programs/safe/issues/issue-87/main.rkt")
        check-safe)
  (test "safe/issues/issue-88.rkt" check-safe)
  (test "safe/issues/issue-89.rkt" check-safe)
  ;; TODO enable once it's fixed
  #;(test '("safe/issues/issue-90/a.rkt"
          "safe/issues/issue-90/b.rkt")
          check-safe)
  (test "safe/issues/issue-91.rkt" check-safe)
  (test "safe/issues/build-vector.rkt" check-safe)
  (test "safe/issues/substruct.rkt" check-safe)
  (test "safe/issues/issue-96.rkt" check-safe)
  (test "safe/issues/hash-basics.rkt" check-safe)
  (test "safe/issues/set-basics.rkt" check-safe)
  (test "safe/issues/parametric-basics.rkt" check-safe)
  (test "safe/issues/issue-97.rkt" check-safe)
  (test "safe/issues/issue-99.rkt" check-safe)
  (test "safe/issues/issue-98.rkt" check-safe)
  (test "safe/issues/issue-101.rkt" check-safe)
  ;(test "safe/issues/issue-101b.rkt" check-safe) ; TODO restore when restore `zo`
  (test "safe/issues/case-lambdas.rkt" check-safe)
  (test "safe/issues/refined-string2list.rkt" check-safe)
  (test "safe/issues/controlled-structs.rkt" check-safe)
  (test "safe/issues/issue-105a.rkt" check-safe)
  (test '("programs/safe/issues/issue-105b.rkt"
          "programs/safe/issues/issue-105c.rkt")
        check-safe)
  (test "safe/issues/issue-102.rkt" check-safe)
  (test "safe/issues/issue-68.rkt" check-safe)
  (test "safe/issues/issue-107.rkt" check-safe) ; FIXME current false poz due to imprecise rest-arg reasoning
  (test "safe/issues/define-contract.rkt" check-safe)
  (test "safe/issues/sub-module.rkt" check-safe)
  (test "safe/issues/base-types.rkt" check-safe)
  (test "safe/issues/base-disjunct.rkt" check-safe)
  (test "safe/issues/thread-cells.rkt" check-safe)
  (test "safe/issues/accum-loop.rkt" check-safe)
  (test "safe/issues/issue-83.rkt" check-safe)
  
  (test "unsafe/issues/list2vector.rkt" check-fail)
  (test "unsafe/issues/oop-encoding.rkt" check-fail)
  (test "unsafe/issues/make-vector.rkt" check-fail)
  (test "unsafe/issues/issue-79.rkt" check-fail)
  (test "unsafe/issues/issue-61.rkt" check-fail)
  (test "unsafe/issues/issue-74a.rkt" check-fail)
  (test "unsafe/issues/issue-74b.rkt" check-fail)
  (test "unsafe/issues/issue-74c.rkt" check-fail)
  ;(test "unsafe/issues/issue-80.rkt" check-fail) ; TODO: check for exn
  (test "unsafe/issues/issue-82.rkt" check-fail)
  (test "unsafe/issues/issue-89.rkt" check-fail)
  (test "unsafe/issues/utilities.rkt" check-fail)
  (test "unsafe/issues/undefined.rkt" check-fail)
  (test "unsafe/issues/build-vector.rkt" check-fail)
  (test "unsafe/issues/substruct.rkt" check-fail)
  (test "unsafe/issues/parametric-basics.rkt" (check 'Failed 2 2))
  (test "unsafe/issues/issue-97.rkt" check-fail)
  (test "unsafe/issues/strict-parametricity.rkt" check-fail)
  (test "unsafe/issues/controlled-structs.rkt" check-fail)
  (test "unsafe/issues/set-basics.rkt" check-fail)
  (test "unsafe/issues/hash-basics.rkt" check-fail)
  (test "unsafe/issues/issue-105.rkt" check-fail)
  (test "unsafe/issues/issue-68.rkt" check-fail)
  (test "unsafe/issues/issue-106.rkt" check-fail)
  (test "unsafe/issues/define-contract.rkt" check-fail)
  (test "unsafe/issues/sub-module.rkt" check-fail)
  (test "unsafe/issues/base-disjunct.rkt" check-fail)
  (test "unsafe/issues/thread-cells.rkt" check-fail)
  (test "unsafe/issues/issue-83.rkt" check-fail)
  (test "unsafe/issues/bogus-prop.rkt" check-fail)

  ;; Slightly larger ones
  (test "safe/real/hash-srfi-69.rkt" (check 'Ok-pos 0 #f)) ; duplicates, depending on counting
  (test "safe/real/fector.rkt" (check 'Ok-pos 0 1))

  (test   "safe/real/leftist-tree.rkt" check-safe)
  (test "unsafe/real/leftist-tree.rkt" check-fail)
  (test   "safe/real/protected-leftist-tree.rkt" check-safe)
  (test "unsafe/real/protected-leftist-tree.rkt" check-fail)

  (test   "safe/real/ring-buffer.rkt" check-safe)
  (test "unsafe/real/ring-buffer.rkt" check-fail)
  
  ;; Multple files
  #;(test '("programs/safe/multiple/main.rkt"
          "programs/safe/multiple/helper-1.rkt"
          "programs/safe/multiple/helper-2.rkt")
        check-safe)
  #;(test '("programs/unsafe/multiple/main.rkt"
          "programs/unsafe/multiple/helper-1.rkt"
          "programs/unsafe/multiple/helper-2.rkt")
        (check 'Failed 1 1))

  ;; From gradual benchmarks
  (test '("gradual-typing-benchmarks/sieve/streams.rkt"
          "gradual-typing-benchmarks/sieve/main.rkt")
        check-safe)
  #;(test '("gradual-typing-benchmarks/morsecode/morse-code-table.rkt"
          "gradual-typing-benchmarks/morsecode/morse-code-strings.rkt"
          "gradual-typing-benchmarks/morsecode/levenshtein.rkt"
          "gradual-typing-benchmarks/morsecode/main.rkt")
        check-safe)
  #;(test '("gradual-typing-benchmarks/fsm/utilities.rkt"
          "gradual-typing-benchmarks/fsm/automata.rkt"
          "gradual-typing-benchmarks/fsm/population.rkt")
        (check 'Ok-pos 2 3))
  #;(test '("gradual-typing-benchmarks/kcfa/structs.rkt"
          "gradual-typing-benchmarks/kcfa/benv.rkt"
          "gradual-typing-benchmarks/kcfa/time.rkt"
          "gradual-typing-benchmarks/kcfa/denotable.rkt")
        check-safe)
  
  (test   "safe/games" check-safe)
  (test "unsafe/games" check-fail)

  ;; big ones
  (test "safe/real/nucleic2-modular-fixed.rkt" (check 'Ok-pos 0 8))
  (test "safe/real/nucleic2-modular.rkt" (check 'Ok-pos 0 10))
  (test "safe/real/slatex.rkt" (check 'Ok-pos 0 22))

  (test   "safe/interp/main.rkt" check-safe)
  (test "unsafe/interp/main.rkt" check-fail)
  )
