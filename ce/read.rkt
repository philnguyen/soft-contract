#lang racket/base
(require "../lang.rkt"
         (rename-in "../read.rkt" [parse-prog parse-prog/raw]))
(provide parse-prog)

(define (parse-prog mods expr)
  (parameterize ([on-•! •!])
    (parse-prog/raw mods expr)))
