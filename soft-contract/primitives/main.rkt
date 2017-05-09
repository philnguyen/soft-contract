#lang typed/racket/base

(provide prims@)

(require typed/racket/unit
         set-extras
         "../ast/main.rkt"
         "../runtime/main.rkt"
         "../signatures.rkt"
         "signatures.rkt"
         "prim-runtime.rkt"
         "relations.rkt"
         "prims-04.rkt"
         "prims-05.rkt"
         "prims-08.rkt"
         "prims-10.rkt"
         "prims-13.rkt"
         "prims-15.rkt"
         "prims-16.rkt"
         "prims-17.rkt"
         "prims-math.rkt"
         )

(define-unit pre-prims@
  (import (prefix rt: prim-runtime^))
  (export prims^)
  (init-depend prim-runtime^)

  (: get-prim : Symbol → (Option -⟦o⟧))
  (define (get-prim o) (hash-ref rt:prim-table o #f))

  (: get-const : Symbol → -prim)
  (define (get-const c)
    (or (hash-ref rt:const-table c #f)
        (hash-ref rt:alias-internal-table c #f)
        (error 'get-const "nothing for ~a" c)))

  (: o⇒o : Symbol Symbol → -R)
  (define (o⇒o p q)
    (cond [(eq? p q) '✓]
          [(∋ (rt:get-weakers p) q) '✓]
          [(∋ (rt:get-exclusions p) q) '✗]
          [else '?]))

  (: get-conservative-range : Symbol → Symbol)
  (define (get-conservative-range o) (hash-ref rt:range-table o (λ () 'any/c)))
  
  (define get-exclusions rt:get-exclusions)

  (: prim-arity : Symbol → Arity)
  (define (prim-arity o)
    (hash-ref rt:arity-table o (λ () (error 'get-arity "nothing for ~a" o))))

  (define extract-list-content rt:extract-list-content)
  )

(define-compound-unit/infer prims@
  (import proof-system^ widening^)
  (export prims^ prim-runtime^)
  (link prim-runtime@
        pre-prims@
        relations@
        prims-04@
        prims-05@
        prims-08@
        prims-10@
        prims-13@
        prims-15@
        prims-16@
        prims-17@
        prims-math@))
