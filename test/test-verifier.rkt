#lang racket/base
(require racket/contract)

(module+ test
  (require racket/match racket/sandbox racket/file rackunit
           "../lang.rkt" "../parse.rkt" "../check.rkt")
  
  (define exn:scv? (or/c exn:fail:contract:counterexample?
                         exn:fail:contract:maybe?))

  (define/contract (verify p)
    (.prog? . -> . (or/c exn:fail:contract:counterexample?
                         exn:fail:contract:maybe?
                         void?))
    (define ans (void))
    (check-not-exn
     (λ ()
       (with-handlers ([exn:scv? (λ (e) (set! ans e))])
         (feedback p))))
    ans)

  ;; Check whether program is safe
  (define/contract (check-verify-safe p)
    (.prog? . -> . any)
    (check-false (exn:scv? (verify p))))

  ;; Check whether program fails, optionally enforcing a counterexample
  (define/contract (check-verify-fail p [counter-example? #f])
    ([.prog?] [boolean?] . ->* . any)
    (define ans (verify p))
    (check-true (exn:scv? ans))
    (when counter-example?
      ;; Ensure mentioning of a counterexample
      (check-true (exn:fail:contract:counterexample? ans))
      ;; Ensure concrete counterexample
      (log-debug "exn message: ~a~n" (exn-message ans))
      (check-false (member #\• (string->list (exn-message ans))))))
  
  ;; Enforce the tool NOT to generate any counterexample
  (define/contract (check-no-ce p)
    (.prog? . -> . any)
    (define ans (verify p))
    (check-true (or (not (exn:scv? ans))
                    (exn:fail:contract:maybe? ans))))
  
  (define (test-dir dir-name test-func)
    (path-string? (.prog? . -> . any) . -> . any)
    (for* ([file (in-directory (format "programs/~a" dir-name))]
           [file-path-str (in-value (path->string file))]
           #:when (regexp-match-exact? #rx".*rkt" file-path-str))
      (printf "Testing: ~a~n" file-path-str)
      (test-case
       file-path-str
       (begin
         (define prog #f)
         (check-not-exn (λ () (set! prog (files->prog (list file-path-str)))))
         (test-func prog)))))

  (test-dir "safe" check-verify-safe)
  (test-dir "fail" check-verify-fail)
  (test-dir "fail-ce" (λ (s) (check-verify-fail s #t)))
  (test-dir "no-ce" check-no-ce))
