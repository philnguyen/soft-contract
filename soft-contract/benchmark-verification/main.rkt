#lang racket/base

(module+ test
  (require racket/cmdline racket/match racket/set racket/list racket/sandbox racket/contract
           racket/file racket/format rackunit
           (only-in racket/file file->list)
           "../utils.rkt" "../show.rkt" "../lang.rkt" "../read.rkt" "../runtime.rkt"
           "../check.rkt" "../main.rkt")
  (define Time-Out 120)

  (define scv:exn? (or/c exn:fail:contract:counterexample? exn:fail:contract:maybe?))
  (define verification-result? (or/c 'timeout 'safe scv:exn?))

  (define-syntax-rule (time-thunk e)
    (time-apply (λ () e) '()))

  (define/contract (count-lines fn)
    (path-string? . -> . integer?)

    (define (code-line? l)
      (not (or (regexp-match-exact? #rx" *" l)
               (regexp-match-exact? #rx" *;.*" l))))
    
    (count code-line? (file->lines fn)))

  (define/contract (fname->tname fname)
    (string? . -> . string?)
    (match fname
      [(regexp #rx"(.+).sch" (list _ name)) name]))

  ;; run program and report result/time
  (define/contract (verify prog)
    (any/c . -> . verification-result?)
    (with-handlers ([scv:exn? values])
      (feedback/massage prog Time-Out)))

  ;; Make sure this correct program is verified
  (define/contract (check-verify-safe prog)
    (any/c . -> . any)
    (check-equal? (verify prog) 'safe))

  ;; Make sure the tool does NOT generate any counterexample for correct program
  ;; (even though it may give a false positive)
  (define/contract (check-no-ce prog)
    (any/c . -> . integer?)
    (check-false (exn:fail:contract:counterexample? (verify prog))))

  ;; Make sure faulty program can't be verified, optionally enforcing a counterexample
  (define/contract (check-verify-fail prog [ce? #f])
    ([any/c] [boolean?] . ->* . any)
    (define a (verify prog))
    (check-true (scv:exn? a))
    (define err-msg (exn-message a))
    (when ce?
      ;; Ensure mentioning of a counterexample
      (check-true (exn:fail:contract:counterexample? a))
      ;; Ensure counterexample is fully concrete
      (check-false (member #\• (string->list err-msg))))
    (log-info "~n~a~n" err-msg))

  (define sum-all-lc 0)
  (define max-all-order 0)
  (define sum-all-t 0)
  (define/contract (test-dir dir-name test-func)
    (path-string? (any/c . -> . any) . -> . any)
    (cond
      [(directory-exists? dir-name)
       (for* ([subdir-name (map path->string (directory-list dir-name))]
              [subdir-path (in-value (format "~a/~a" dir-name subdir-name))]
             #:when (directory-exists? subdir-path))
         (printf "~a:~n" subdir-path)
         (define fnames (sort (map path->string (directory-list subdir-path)) string<=?))
         (define sum-lc 0)
         (define max-order 0)
         (define sum-t 0)
         (for ([fname fnames] #:when (regexp-match-exact? #rx".*sch" fname))
           (define path (format "~a/~a" subdir-path fname))
           (define lc (count-lines path))
           (collect-garbage) (collect-garbage) (collect-garbage)
           (define-values (r t₁ t₂ t₃)
             (time-thunk (test-case path (test-func (file->list path)))))
           (define t t₂ #;(/ t₂ 1000))
           (define ord (order (read-p (file->list path))))
           (printf "  ~a & ~a & ~a & ~a \\\\~n"
                   (fname->tname fname) lc ord t)
           (set! sum-lc (+ sum-lc lc))
           (set! max-order (max max-order ord))
           (set! sum-t (+ sum-t t)))
         (printf "Summary for\"~a\" & ~a & ~a & ~as \\\\~n"
                 subdir-name sum-lc max-order sum-t)
         (set! sum-all-lc (+ sum-all-lc sum-lc))
         (set! max-all-order (max max-all-order max-order))
         (set! sum-all-t (+ sum-all-t sum-t)))]
      [else (printf "~nWarning: directory \"~a\" does not exist~n" dir-name)]))

  (test-dir "safe" check-verify-safe)
  (test-dir "fail-ce" (λ (s) (check-verify-fail s #t)))
  (test-dir "fail" check-verify-fail)
  (test-dir "no-ce" check-no-ce)
  (printf "Summary for all & ~a & ~a & ~as \\\\~n"
          sum-all-lc max-all-order sum-all-t))
