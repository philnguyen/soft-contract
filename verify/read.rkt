#lang racket/base
(require "../lang.rkt"
         (rename-in "../read.rkt" [read-p read-p/raw]))
(provide read-p)

(define (read-p s)
  (gen-havoc (read-p/raw s)))
