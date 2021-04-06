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

(define TIMEOUT 2000)

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
  (test '("programs/safe/issues/re-exported-struct/posn-untyped.rkt"
          "programs/safe/issues/re-exported-struct/posn-typed.rkt")
        check-safe)
  (test '("programs/safe/issues/struct-out-twice/m1.rkt"
          "programs/safe/issues/struct-out-twice/m2.rkt"
          "programs/safe/issues/struct-out-twice/m3.rkt"
          "programs/safe/issues/struct-out-twice/main.rkt")
        check-safe)
  (test '("programs/safe/issues/struct-out-twice/data.rkt"
          "programs/safe/issues/struct-out-twice/data-adaptor.rkt")
        check-safe)
  (test "safe/issues/literals-as-contracts.rkt" check-safe)
  (test "safe/issues/index-huh.rkt" check-safe)
  (test '("programs/safe/issues/re-provide/posn.rkt"
          "programs/safe/issues/re-provide/main.rkt")
        check-safe)
  (test '("programs/safe/issues/re-provide-struct-twice/data.rkt"
          "programs/safe/issues/re-provide-struct-twice/data-adaptor.rkt"
          "programs/safe/issues/re-provide-struct-twice/const.rkt")
        check-safe)
  (test "safe/issues/sqrt.rkt" check-safe)
  (test "safe/issues/file2list.rkt" check-safe)
  (test '("programs/safe/issues/re-provide-substruct/structs.rkt"
          "programs/safe/issues/re-provide-substruct/adapted.rkt")
        check-safe)
  (test '("programs/safe/issues/submodule-id/adapter.rkt"
          "programs/safe/issues/submodule-id/main.rkt")
        (check 'Ok-pos 0 #f))
  (test "safe/issues/ho-disjunct.rkt" check-safe)
  (test "safe/issues/sub-exn.rkt" check-safe)
  (test "safe/issues/flonum.rkt" check-safe)
  (test "safe/issues/parameters.rkt" check-safe)
  (test "safe/issues/parameter-contract.rkt" check-safe)
  (test "safe/issues/except-in-setc.rkt" check-safe)
  (test "safe/issues/unsafe-vector-star.rkt" check-safe)
  (test "safe/issues/top-struct.rkt" check-safe)
  (test "safe/issues/exported-function-list.rkt" check-safe)
  (test "safe/issues/issue-125.rkt" check-safe)
  (test "safe/issues/io-primitives.rkt" check-safe)

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
  (test "unsafe/issues/exported-function-list.rkt" check-fail)
  (test '("programs/unsafe/issues/re-exported-struct/posn-untyped.rkt"
          "programs/unsafe/issues/re-exported-struct/posn-typed.rkt")
        check-fail)
  (test '("programs/unsafe/issues/struct-out-twice/m1.rkt"
          "programs/unsafe/issues/struct-out-twice/m2.rkt"
          "programs/unsafe/issues/struct-out-twice/m3.rkt"
          "programs/unsafe/issues/struct-out-twice/main.rkt")
        check-fail)
  (test '("programs/unsafe/issues/struct-out-twice/data.rkt"
          "programs/unsafe/issues/struct-out-twice/data-adaptor.rkt")
        check-fail)
  (test "unsafe/issues/literals-as-contracts.rkt" check-fail)
  (test "unsafe/issues/index-huh.rkt" check-fail)
  (test '("programs/unsafe/issues/re-provide/posn.rkt"
          "programs/unsafe/issues/re-provide/main.rkt")
        check-fail)
  (test '("programs/unsafe/issues/re-provide-struct-twice/data.rkt"
          "programs/unsafe/issues/re-provide-struct-twice/data-adaptor.rkt"
          "programs/unsafe/issues/re-provide-struct-twice/const.rkt")
        check-fail)
  (test "unsafe/issues/sqrt.rkt" check-fail)
  (test "unsafe/issues/file2list.rkt" check-fail)
  (test '("programs/unsafe/issues/re-provide-substruct/structs.rkt"
          "programs/unsafe/issues/re-provide-substruct/adapted.rkt")
        check-fail)
  (test '("programs/unsafe/issues/opaque/lib.rkt"
          "programs/unsafe/issues/opaque/user.rkt")
        check-fail)
  (test "unsafe/issues/ho-disjunct.rkt" check-fail)
  (test "unsafe/issues/sub-exn.rkt" check-fail)
  (test "unsafe/issues/flonum.rkt" check-fail)
  (test "unsafe/issues/parameters.rkt" check-fail)
  (test "unsafe/issues/parameter-contract.rkt" check-fail)
  (test "unsafe/issues/except-in-setc.rkt" check-fail)
  (test "unsafe/issues/unsafe-vector-star.rkt" check-fail)
  (test "unsafe/issues/two-calls.rkt" check-fail)
  (test "unsafe/issues/sequential-calls.rkt" check-fail)
  (test "unsafe/issues/reverse-args.rkt" check-fail)
  (test "unsafe/issues/guarded-first-order.rkt" check-fail)
  (test "unsafe/issues/issue-125.rkt" (check 'Failed 5 #f))
  (test "unsafe/issues/io-primitives.rkt" check-fail)

  ;; Slightly larger ones
  (test "safe/real/hash-srfi-69.rkt" (check 'Ok-pos 0 #f)) ; duplicates, depending on counting
  (test "safe/real/fector.rkt" (check 'Ok-pos 0 2))

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

  (test   "safe/interp/main.rkt" check-safe)
  (test "unsafe/interp/main.rkt" check-fail)

  (test "safe/games/snake.rkt" check-safe)
  (test "safe/games/tetris.rkt" check-safe)
  (test "safe/games/zombie.rkt" check-safe)
  (test '("programs/safe/games/snake-files/data.rkt"
          "programs/safe/games/snake-files/data-adaptor.rkt"
          "programs/safe/games/snake-files/const.rkt"
          "programs/safe/games/snake-files/collide.rkt"
          "programs/safe/games/snake-files/cut-tail.rkt"
          "programs/safe/games/snake-files/motion-help.rkt"
          "programs/safe/games/snake-files/motion.rkt"
          "programs/safe/games/snake-files/handlers.rkt"
          "programs/safe/games/snake-files/main.rkt"
          )
          (check 'Ok-pos 1 1))
  (test "unsafe/games" check-fail)

  ;; big ones
  (test "safe/real/nucleic2-modular-fixed.rkt" (check 'Ok-pos 0 8))
  (test "safe/real/nucleic2-modular.rkt" (check 'Ok-pos 0 10))
  (test "safe/real/slatex.rkt" (check 'Ok-pos 0 22))
  )
