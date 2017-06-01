#lang typed/racket/base

(provide (all-defined-out))

(require typed/racket/unit
         "../ast/definition.rkt")

(define-signature parser-helper^
  ([parse-files : ((Listof Path-String) → (Listof -module))]))

(struct exn:missing exn:fail ([path : Path-String]) #:transparent)
