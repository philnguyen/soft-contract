#lang typed/racket/base

(provide prim-runtime^)

(require typed/racket/unit
         set-extras
         "../ast/main.rkt"
         "../runtime/main.rkt")

(define-signature prim-runtime^
  ([add-implication! : (Symbol Symbol → Void)]
   [add-exclusion! : (Symbol Symbol → Void)]))
