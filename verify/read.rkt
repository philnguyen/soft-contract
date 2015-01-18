#lang racket/base
(require "../lang.rkt"
         (rename-in "../read.rkt" [read-prog read-prog/raw]))
(provide read-prog)

(define (read-prog s)
  (gen-havoc (read-prog/raw s)))
