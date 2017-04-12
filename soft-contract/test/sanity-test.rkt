#lang typed/racket/base

(require racket/match
         racket/set
         racket/file
         racket/string
         racket/bool
         typed/rackunit
         "../utils/main.rkt"
         "../runtime/main.rkt"
         "../run.rkt")

(define TIMEOUT 1200)

(: run-handler (∀ (α) ((℘ -ΓA) → α) Path-String → α))
(define (run-handler f p)
  ;; Can't use time-apply
  (define t₀ (current-milliseconds))
  (printf "~a~n" p)
  (define-values (As Σ) (havoc-file p))
  (printf "  ~a~n" (- (current-milliseconds) t₀))
  (define-values (_ ΓEs) (set-partition (λ ([ΓA : -ΓA]) (-W? (-ΓA-ans ΓA))) As))
  (f ΓEs))

(: check : Any (Option Natural) (Option Natural) → (℘ -ΓA) → Any)
(define ((check msg lo hi) ΓEs)
  (define n (set-count ΓEs))
  (cond
    [(and (implies lo (<= lo n)) (implies hi (<= n hi)))
     (printf "  ✓ ~a~n" msg)]
    [else
     (fail
     (format "Expect numberof blames in range ⟨~a,~a⟩, got ~a" (or lo '-∞) (or hi '+∞) n))]))

(define check-safe (check 'Safe 0 0))
(define check-fail (check 'Failed 1 #f))

(: test : Path-String ((℘ -ΓA) → Any) → Any)
(define (test path f)

  (define (run-on-file [fn : Path-String])
    (when (regexp-match-exact? #rx".*rkt" fn)
      (test-case fn
        (with-handlers ([exn?
                         (λ ([e : exn])
                           (fail (format "Exception: ~a~n" (exn-message e))))])
          (unless (with-time-limit : Any TIMEOUT (run-handler f fn))
            (fail (format "Timeout after ~a seconds" TIMEOUT)))))))

  (define path* (format "programs/~a" path))
  (cond
    [(directory-exists? path*)
     (for ([file-path (in-directory path*)])
       (run-on-file (path->string file-path)))]
    [else
     (run-on-file path*)]))

(module+ test
  ;; Order doesn't matter. I just run shorter ones first
  (test   "safe/octy" check-safe)
  (test "unsafe/octy" check-fail)
  
  (test   "safe/softy" check-safe)
  (test "unsafe/softy" check-fail)
  
  (test   "safe/misc" check-safe)
  (test "unsafe/misc" check-fail)

  (test "paper/match.rkt" check-safe)
  (test "paper/match-no-check.rkt" check-safe)
  (test "paper/match-unsafe.rkt" check-fail)
  (test "paper/escape.rkt" check-safe)
  (test "paper/escape-conservative.rkt" (check 'Failed 1 1))
  (test "paper/factorial.rkt" check-safe)
  (test "paper/havoc-1.rkt" check-fail)
  (test "paper/havoc-2.rkt" check-fail)
  (test "paper/mutable-box-as-closure.rkt" check-safe)
  (test "paper/succ.rkt" check-safe)
  (test "paper/succ-incorrect.rkt" check-fail)

  (test "safe/issues/cons-of-list.rkt" check-safe)
  (test "safe/issues/list2vector.rkt" check-safe)
  (test "unsafe/issues/list2vector.rkt" check-fail)

  (test "safe/real/hash-srfi-69.rkt" (check 'Ok-pos 1 1))

  (test   "safe/real/protected-leftist-tree.rkt" check-safe)
  (test "unsafe/real/protected-leftist-tree.rkt" check-safe)

  (test   "safe/real/protected-ring-buffer.rkt" check-safe)
  (test "unsafe/real/protected-ring-buffer.rkt" check-fail)
  
  (test   "safe/games" check-safe)
  (test "unsafe/games" check-fail))
