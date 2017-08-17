#lang typed/racket/base

(provide prims@)

(require typed/racket/unit
         set-extras
         "../ast/main.rkt"
         "../runtime/signatures.rkt"
         "../proof-relation/signatures.rkt"
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
         )

(define-unit pre-prims@
  (import (prefix rt: prim-runtime^))
  (export prims^)
  (init-depend prim-runtime^)

  (: get-prim : Symbol → -Prim)
  (define (get-prim o)
    (hash-ref rt:prim-table o (λ () (error 'get-prim "nothing for ~a" o))))

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
    (hash-ref rt:arity-table o (λ () (error 'prim-arity "don't know `~a`'s arity~n" o))))

  (define extract-list-content rt:extract-list-content)

  (: parse-prim : Identifier → (Option -prim))
  (define (parse-prim id)
    (cond [(parse-prim-table-ref rt:const-table id (λ () #f)) => values]
          [(alias-table-ref rt:alias-table id (λ () #f)) => parse-prim]
          [else #f]))
  )

(define-compound-unit/infer prims@
  (import proof-system^ local-prover^ widening^ app^ kont^ compile^ for-gc^
          val^ pc^ sto^ instr^ pretty-print^ env^ mon^)
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
        prims-math@))
