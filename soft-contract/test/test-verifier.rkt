#lang typed/racket/base

(require racket/match
         racket/set
         racket/file
         racket/string
         typed/rackunit
         "../utils/set.rkt"
         "../runtime/main.rkt"
         "../reduction/main.rkt")

(: check-verify-safe : Path-String → Any)
(define (check-verify-safe p)
  (define-values (As _₁ _₂) (havoc-file p))
  (define-values (_ ΓEs) (set-partition -ΓW? As))
  (printf "Verifing ~a: " p)
  (cond
    [(set-empty? ΓEs)
     (define msg
       (let ([blm-msgs
              (for/list : (Listof String) ([ΓE ΓEs])
                (match-define (-ΓE _ blm) ΓE)
                (format "  - ~a" (show-blm blm)))])
         (string-join blm-msgs
                      "\n"
                      #:before-first "✗"
                      #:after-last "\n")))
     (fail msg)]
    [else (printf " ✓~n")]))

(: with-dir : Path-String (Path-String → Any) → Any)
(define (with-dir dir f)
  (for* ([file (in-directory (format "programs/~a" dir))]
         [file-path-str (in-value (path->string file))]
         #:when (regexp-match-exact? #rx".*rkt" file-path-str))
    (test-case file-path-str
      (f file-path-str))))

(module+ test
  (with-dir "safe" check-verify-safe))
