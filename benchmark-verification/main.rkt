#lang racket/base

(module+ test
  (require racket/cmdline racket/match racket/set racket/list racket/sandbox racket/contract
           rackunit racket/file racket/format
           (only-in racket/file file->list)
           "../utils.rkt" "../show.rkt" "../lang.rkt" "../runtime.rkt" "../check.rkt")

  (define Time-Out 300)

  (define scv:exn? (or/c exn:fail:contract:counterexample? exn:fail:contract:maybe?))
  (define verification-result? (or/c 'timeout 'safe scv:exn?))

  ;; run program and report result/time
  (define/contract (verify prog)
    (any/c . -> . (values verification-result? integer?))
    
    (define (run)
      (with-handlers ([scv:exn? values])
        (feedback prog Time-Out)))
    
    (match-define-values ((list res) t₁ t₂ t₃)
                         (time-apply run '()))
    
    (values res t₂))

  ;; Make sure this correct program is verified
  (define/contract (check-verify-safe prog)
    (any/c . -> . any)
    (define-values (a t) (verify prog))
    (check-equal? a 'safe)
    (printf "~as" (~r (/ t 1000) #:precision 3)))

  ;; Make sure faulty program can't be verified, optionally enforcing a counterexample
  (define/contract (check-verify-fail prog [ce? #f])
    ([any/c] [boolean?] . ->* . any)
    (define-values (a t) (verify prog))
    (printf "~as" (~r (/ t 1000) #:precision 3))
    (check-true (scv:exn? a))
    (define err-msg (exn-message a))
    (when ce?
      ;; Ensure mentioning of a counterexample
      (check-true (exn:fail:contract:counterexample? a))
      ;; Ensure counterexample is fully concrete
      (check-false (member #\• (string->list err-msg))))
    (printf "~n~a~n" err-msg))

  ;; Make sure the tool does NOT generate any counterexample for correct program
  ;; (even though it may give a false positive)
  (define/contract (check-no-ce prog)
    (any/c . -> . integer?)
    (define-values (a t) (verify prog))
    (check-false (exn:fail:contract:counterexample? a)))

  (define/contract (test-dir dir-name test-func)
    (path-string? (any/c . -> . any) . -> . any)
    (cond
      [(directory-exists? dir-name)
       (define fnames (sort (map path->string (directory-list dir-name)) string<=?))
       (for ([fname fnames] #:when (regexp-match-exact? #rx".*sch" fname))
         (define path (format "~a/~a" dir-name fname))
         (printf "~nChecking \"~a\": " path)
         (test-case path (test-func (file->list path))))]
      [else (printf "Warning: directory \"~a\" does not exist~n" dir-name)]))
  
  (test-dir "safe" check-verify-safe)
  (test-dir "fail-ce" (λ (s) (check-verify-fail s #t)))
  (test-dir "fail" check-verify-fail)
  (test-dir "no-ce" check-no-ce))
