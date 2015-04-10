#lang racket/base

(require "../parse.rkt")
(require rackunit)

(for* ([dir (list "programs/safe" "programs/fail" "programs/fail-ce")]
       [file (in-directory dir)]
       #:when (regexp-match-exact? #rx".*rkt" (path->string file)))
  (define str (path->string file))
  (cond
    [(directory-exists? file)
     (printf "Dir: ~a~n" file)]
    #;[(regexp-match-exact? #rx".*rkt" (path->string file))
     (printf "Rkt: ~a~n" file)
     (test-case str (test-not-exn str (λ () (files->prog (list str)))))]))
