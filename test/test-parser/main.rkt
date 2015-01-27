#lang racket/base

(module+ test
  (require "../../parse.rkt" "../../expand.rkt")
  (require rackunit)
  
  (for ([file (in-directory "tests")]
        #:when (regexp-match-exact? #rx".*rkt" (path->string file)))
    (define str (path->string file))
    (printf "Test parsing ~a~n" str)
    (test-case str (test-not-exn str (λ () (files->prog (list str)))))))
