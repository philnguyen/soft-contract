#lang racket/base

(module+ test
  (require racket/cmdline racket/match racket/set racket/list racket/sandbox racket/contract
           racket/file racket/format rackunit
           (only-in racket/file file->list)
           "../utils.rkt" "../show.rkt" "../lang.rkt" "../read.rkt" "../runtime.rkt"
           "../check.rkt" "../main.rkt")
  (define Time-Out 120)
  (define Iters 10)

  (define scv:exn? (or/c exn:fail:contract:counterexample? exn:fail:contract:maybe?))
  (define verification-result? (or/c 'timeout 'safe scv:exn?))

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
    (any/c . -> . (values verification-result? real?))
    (define-values (a Σt)
      (for/fold ([a #f] [Σt 0]) ([_ (in-range Iters)])
        (collect-garbage) (collect-garbage) (collect-garbage)
        (define-values (a t₁ t₂ t₃)
          (time-apply (λ ()
                        (with-handlers ([scv:exn? values])
                          (feedback/massage prog Time-Out)))
                      '()))
        (values a (+ Σt t₂))))
    (values (car a) (/ Σt Iters)))

  ;; Make sure this correct program is verified
  (define/contract (check-verify-safe prog)
    (any/c . -> . real?)
    (define-values (a t) (verify prog))
    (check-equal? a 'safe)
    t)

  ;; Make sure the tool does NOT generate any counterexample for correct program
  ;; (even though it may give a false positive)
  (define/contract (check-no-ce prog)
    (any/c . -> . real?)
    (define-values (a t) (verify prog))
    (check-false (exn:fail:contract:counterexample? a))
    t)

  ;; Make sure faulty program can't be verified, optionally enforcing a counterexample
  (define/contract (check-verify-fail prog [ce? #f])
    ([any/c] [boolean?] . ->* . real?)
    (define-values (a t) (verify prog))
    (check-true (scv:exn? a))
    (define err-msg (exn-message a))
    (when ce?
      ;; Ensure mentioning of a counterexample
      (check-true (exn:fail:contract:counterexample? a))
      ;; Ensure counterexample is fully concrete
      (check-false (member #\• (string->list err-msg))))
    (log-info "~n~a~n" err-msg)
    t)

  (define-values (sum-all-lc sum-all-cc max-all-order sum-all-t) (values 0 0 0 0))
  (define/contract (test-dir dir-name test-func)
    (path-string? (any/c . -> . real?) . -> . any)
    (cond
      [(directory-exists? dir-name)
       (for* ([subdir-name (map path->string (directory-list dir-name))]
              [subdir-path (in-value (format "~a/~a" dir-name subdir-name))]
             #:when (directory-exists? subdir-path))
         (printf "~a:~n" subdir-path)
         (define fnames (sort (map path->string (directory-list subdir-path)) string<=?))
         (define-values (sum-lc sum-cc max-order sum-t) (values 0 0 0 0))
         (for ([fname fnames] #:when (regexp-match-exact? #rx".*sch" fname))
           (define path (format "~a/~a" subdir-path fname))
           (define sexp (file->list path))
           (define-values (lc cc ord t)
             (values (count-lines path)
                     (checks# (read-p sexp))
                     (order (read-p sexp))
                     (test-func sexp)))
           (printf "  ~a & ~a & ~a & ~a & ~a \\\\~n"
                   (fname->tname fname) lc cc ord (~r t #:precision 1))
           (set!-values (sum-lc sum-cc max-order sum-t)
                        (values (+ sum-lc lc)
                                (+ sum-cc cc)
                                (max max-order ord)
                                (+ sum-t t))))
         (printf "Summary for \"~a\" & ~a & ~a & ~a & ~as \\\\~n"
                 subdir-name sum-lc sum-cc max-order sum-t)
         (set!-values (sum-all-lc sum-all-cc max-all-order sum-all-t)
                      (values (+ sum-all-lc sum-lc)
                              (+ sum-all-cc sum-cc)
                              (max max-all-order max-order)
                              (+ sum-all-t sum-t))))]
      [else (printf "~nWarning: directory \"~a\" does not exist~n" dir-name)]))

  (test-dir "safe" check-verify-safe)
  (test-dir "fail-ce" (λ (s) (check-verify-fail s #t)))
  (test-dir "fail" check-verify-fail)
  (test-dir "no-ce" check-no-ce)
  (printf "Summary for all & ~a & ~a & ~a & ~as \\\\~n"
          sum-all-lc sum-all-lc max-all-order sum-all-t))
