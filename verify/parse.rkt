#lang racket/base
(require "../lang.rkt"
         (rename-in "../read.rkt" [parse-prog parse-prog/raw]))
(provide parse-prog)

(define (parse-prog mods expr)
  (gen-havoc (parse-prog/raw mods expr)))
