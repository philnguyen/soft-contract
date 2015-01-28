#lang racket/base
(require racket/contract)

(module+ test
  (require racket/match racket/sandbox racket/file rackunit)
  (define (make-ev)
    (parameterize ([sandbox-output 'string]
                   [sandbox-error-output 'string]
                   [sandbox-propagate-exceptions #f]
                   [sandbox-memory-limit 200]
                   [sandbox-eval-limits (list 60 200)]
                   [sandbox-namespace-specs
                    (append (sandbox-namespace-specs)
                            `(file/convertible
                              json))]
                   [sandbox-path-permissions (list* ; FIXME hack²
                                              (list 'exists "/")
                                              (list 'execute "/bin/sh")
                                              '((read #rx#"racket-prefs.rktd")))])
      (make-evaluator 'soft-contract)))

  (define/contract (verify s)
    (string? . -> . (values string? string? string?))
    (define ev (make-ev))
    (define val (ev s))
    (define out (get-output ev))
    (define err (get-error-output ev))
    (values val out err))

  ;; Check whether program is safe
  (define/contract (check-verify-safe s)
    (string? . -> . any)
    (define-values (val out err) (verify s))
    (test-equal? "no error" "" err)
    (test-true "safe" (regexp-match? ".*Program is safe.*" out)))

  ;; Check whether program fails, optionally enforcing a counterexample
  (define/contract (check-verify-fail s [counter-example? #f])
    (string? . -> . any)
    (define-values (val out err) (verify s))
    (check-regexp-match ".*ontract violation.*" err)
    (when counter-example?
      ;; Ensure mentioning of a counterexample
      (check-regexp-match ".*An example module that breaks it.*" err)
      ;; Ensure concrete counterexample
      (check-false (member #\• (string->list err)))))
  
  ;; Enforce the tool NOT to generate any counterexample
  (define/contract (check-no-ce s)
    (define-values (val out err) (verify s))
    (check-false (regexp-match? ".*An example module that breaks it.*" err)))
  
  ;; String (String -> Void) -> Void
  (define (test-dir dir-name test-func)
    (for ([file (in-directory dir-name)]
          #:when (regexp-match-exact? #rx".*rkt" (path->string file)))
      (printf "Testing: ~a~n" file)
      (test-case (path->string file)
                 (test-func (format "(~a)" (file->string file))))))

  (test-dir "safe" check-verify-safe)
  (test-dir "fail" check-verify-fail)
  (test-dir "fail-ce" (λ (s) (check-verify-fail s #t)))
  (test-dir "no-ce" check-no-ce))
