#lang typed/racket/base

(require racket/match
         racket/set
         racket/file
         racket/string
         typed/rackunit
         "../utils/main.rkt"
         "../runtime/main.rkt"
         "../reduction/quick-step.rkt")

(: check-verify-safe : Path-String → Any)
(define (check-verify-safe p)
  (define-values (As Σ) (havoc-file p))
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
        (define TIMEOUT 600)
        (unless (within-time: Any TIMEOUT (f file-path-str))
          (fail (format "Timeout after ~a seconds" TIMEOUT)))))))

(module+ test
  (with-dir "safe" check-verify-safe))
