#lang racket/base

(module+ test
  (require "../parse.rkt")
  (require rackunit)
  
  (for* ([dir (list "test-verifier/safe" "test-verifier/fail" "test-verifier/fail-ce")]
         [file (in-directory dir)]
         #:when (regexp-match-exact? #rx".*rkt" (path->string file)))
    (define str (path->string file))
    (printf "Test parsing ~a~n" str)
    (test-case str (test-not-exn str (λ () (files->prog (list str)))))))
