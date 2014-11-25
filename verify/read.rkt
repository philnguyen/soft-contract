#lang racket/base
(require racket/match racket/set racket/list
         "../utils.rkt" "../lang.rkt"
         (rename-in "../read.rkt" [read-p read-p/raw])
         (only-in redex variable-not-in))
(provide read-p)

(define (read-p s)
  (gen-havoc (read-p/raw s)))
