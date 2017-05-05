#lang typed/racket/base

(provide parser-helper^)

(require typed/racket/unit
         "../ast/definition.rkt")

(define-signature parser-helper^
  ([parse-files : ((Listof Path-String) → (Listof -module))]))
