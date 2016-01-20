#lang typed/racket/base

(require
 racket/match racket/sandbox racket/file typed/rackunit
 "../check.rkt")

(: verify : Path-String → (U Void exn:scv))
(define (verify p)
  (define ans : (U Void exn:scv) (void))
  (check-not-exn
   (λ ()
     (with-handlers ([exn:scv? (λ ([e : exn:scv]) (set! ans e))])
       (analyze p #:timeout-ok? #f))))
  ans)

(: check-verify-safe : Path-String → Any)
;; Check whether program is safe
(define (check-verify-safe p)
  (check-false (exn:scv? (verify p))))

(: check-verify-fail ([Path-String] [Boolean] . ->* . Any))
;; Check whether program fails, optionally enforcing a counterexample
(define (check-verify-fail p [counter-example? #f])
  (define ans (verify p))
  (check-true (exn:scv? ans))
  (assert (exn:scv? ans)) ; hack for TR
  (when counter-example?
    ;; Ensure mentioning of a counterexample
    (check-true (exn:fail:contract:counterexample? ans))
    ;; Ensure concrete counterexample
    (log-debug "exn message: ~a~n" (exn-message ans))
    #;(check-false (member #\• (string->list (exn-message ans))))))


(: check-no-ce : Path-String → Any)
;; Enforce the tool NOT to generate any counterexample
(define (check-no-ce p)
  (define ans (verify p))
  (check-true (or (not (exn:scv? ans))
                  (exn:fail:contract:maybe? ans))))

(: test-dir : Path-String (Path-String → Any) → Any)
(define (test-dir dir-name test-func)
  (for* ([file (in-directory (format "programs/~a" dir-name))]
         [file-path-str (in-value (path->string file))]
         #:when (regexp-match-exact? #rx".*rkt" file-path-str))
    (printf "Testing: ~a~n" file-path-str)
    (test-case
     file-path-str
     (begin ; TODO: why did I do this?
       (define prog-path : (Option Path-String) #f)
       (check-not-exn (λ () (set! prog-path file-path-str)))
       (test-func (assert #|hack for TR|# prog-path))))))

(test-dir "safe" check-verify-safe)
;(test-dir "fail" check-verify-fail)
;(test-dir "fail-ce" (λ (s) (check-verify-fail s #t)))
;(test-dir "no-ce" check-no-ce)
