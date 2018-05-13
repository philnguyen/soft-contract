#lang typed/racket/base

(provide prims@)

(require typed/racket/unit
         set-extras
         "../ast/main.rkt"
         "../runtime/signatures.rkt"
         "../reduction/signatures.rkt"
         "../signatures.rkt"
         "signatures.rkt"
         "prim-runtime.rkt"
         "relations.rkt"
         "prims-04.rkt"
         "prims-05.rkt"
         "prims-08.rkt"
         "prims-09.rkt"
         "prims-10.rkt"
         "prims-13.rkt"
         "prims-15.rkt"
         "prims-16.rkt"
         "prims-17.rkt"
         "prims-math.rkt"
         "prims-zo.rkt"
         "prims-scv.rkt"
         )

(define-unit pre-prims@
  (import (prefix rt: prim-runtime^))
  (export prims^)
  (init-depend prim-runtime^)

  (: get-prim : Symbol → ⟦F⟧^)
  (define (get-prim o)
    (hash-ref rt:prim-table o (λ () (error 'get-prim "nothing for ~a" o))))

  (: o⊢o : Symbol Symbol → ?Dec)
  (define (o⊢o p q)
    (cond [(eq? p q) '✓]
          [(∋ (rt:get-weakers p) q) '✓]
          [(∋ (rt:get-exclusions p) q) '✗]
          [else #f]))

  (: get-conservative-range : Symbol → Symbol)
  (define (get-conservative-range o) (hash-ref rt:range-table o (λ () 'any/c)))
  
  (define get-exclusions rt:get-exclusions)

  (: prim-arity : Symbol → Arity)
  (define (prim-arity o)
    (hash-ref rt:arity-table o (λ () (error 'prim-arity "don't know `~a`'s arity~n" o))))

  (: parse-prim : Identifier → (Option -prim))
  (define (parse-prim id)
    (cond [(parse-prim-table-ref rt:const-table id (λ () #f)) => values]
          [(alias-table-ref rt:alias-table id (λ () #f)) => parse-prim]
          [else #f]))

  (define implement-predicate rt:implement-predicate)
  (define vec-len rt:vec-len)
  )

(define-compound-unit/infer prims@
  (import ast-pretty-print^ static-info^ meta-functions^
          val^ env^ evl^
          prover^
          alloc^ compile^ step^ mon^ approx^)
  (export prims^ prim-runtime^)
  (link prim-runtime@
        pre-prims@
        relations@
        prims-04@
        prims-05@
        prims-08@
        prims-09@
        prims-10@
        prims-13@
        prims-15@
        prims-16@
        prims-17@
        prims-math@
        prims-zo@
        prims-scv@
        ))
