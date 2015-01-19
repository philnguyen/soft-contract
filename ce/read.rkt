#lang racket/base
(require "../lang.rkt"
         (rename-in "../read.rkt" [read-p read-p/raw]))
(provide read-p)

(define (read-p s)
  (parameterize ([on-•! •!])
    (read-p/raw s)))
