#lang typed/racket/base

(require racket/match
         typed/racket/unit
         "ast/main.rkt"
         "runtime/main.rkt"
         "verifier.rkt"
         "proof-relation/main.rkt"
         "reduction/main.rkt"
         "primitives/main.rkt"
         "parse/main.rkt"
         "primitives/signatures.rkt"
         "reduction/signatures.rkt"
         "signatures.rkt"
         )

(provide lib@)

(define-unit lib@
  (import parser^ compile^ havoc^ reduction^)
  (export lib^)

  (: verify : Syntax (HashTable Symbol Syntax) → Any)
  ;; Given module and contracts, return unverified identifiers
  ;; TODO: so we only care about these explicit boundaries?
  (define (verify stx dec-stxs)
    (with-initialized-static-info
      (match-define (-module p body) (parse-module stx))
      (define decs
        (-provide
         (for/list : (Listof -provide-spec) ([(x c) (in-hash dec-stxs)]
                                             [i : Natural (in-naturals)])
           (-p/c-item x (parse-expr c) (loc->ℓ (loc 'lib-gen i 0 '()))))))
      (define ms (list (-module p `(,@body ,decs))))
      (define-values (As Σ) (run (↓ₚ ms (gen-havoc-expr ms))))
      As)))

(define-values/invoke-unit/infer
  (export lib^)
  (link env@ sto@ val@ instr@ pc@ pretty-print@
        prims@ proof-system@ reduction@ verifier@ parser@ for-gc@
        lib@))
