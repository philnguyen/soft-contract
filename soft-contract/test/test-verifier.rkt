#lang typed/racket/base

(require racket/match
         racket/set
         racket/file
         racket/string
         typed/rackunit
         "../utils/main.rkt"
         "../runtime/main.rkt"
         "../run.rkt")

(define TIMEOUT 300)

(: check-verify-safe : Path-String → Any)
(define (check-verify-safe p)
  ;; Can't use time-apply
  (define t₀ (current-milliseconds))
  (printf "~a~n" p)
  (define-values (As Σ) (havoc-file p))
  (printf "  ~a~n" (- (current-milliseconds) t₀))
  (define-values (_ ΓEs) (set-partition (λ ([ΓA : -ΓA]) (-W? (-ΓA-ans ΓA))) As))
  (cond
    [(set-empty? ΓEs)
     (printf " ✓~n")]
    [else
     (define msg
       (let ([blm-msgs
              (for/list : (Listof String) ([ΓE ΓEs])
                (match-define (-ΓA _ (? -blm? blm)) ΓE)
                (format "  - ~a" (show-blm blm)))])
         (string-join blm-msgs
                      "\n"
                      #:before-first "✗"
                      #:after-last "\n")))
     (fail msg)]))

(: with-dir : Path-String (Path-String → Any) → Any)
(define (with-dir dir f)
  (for* ([file (in-directory (format "programs/~a" dir))]
         [file-path-str (in-value (path->string file))]
         #:when (regexp-match-exact? #rx".*rkt" file-path-str))
    (test-case file-path-str
      (with-handlers ([exn?
                       (λ ([e : exn])
                         (fail (format "Exception: ~a~n" (exn-message e))))])
        (unless (within-time: Any TIMEOUT (f file-path-str))
          (fail (format "Timeout after ~a seconds" TIMEOUT)))))))

(module+ test ; quick sanity check
  (with-dir "safe/octy" check-verify-safe)
  (with-dir "safe/games" check-verify-safe))
