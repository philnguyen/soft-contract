#lang typed/racket/base

(provide (all-defined-out))

(require (for-syntax racket/base
                     (only-in typed/racket/base index?)
                     racket/syntax
                     racket/match
                     racket/list
                     racket/contract
                     racket/pretty
                     syntax/parse
                     syntax/parse/define
                     "def-utils.rkt"
                     (only-in "../utils/pretty.rkt" n-sub))
         racket/contract
         racket/match
         racket/set
         racket/splicing
         racket/promise
         syntax/parse/define
         set-extras
         "../utils/map.rkt"
         "../ast/signatures.rkt"
         "../runtime/signatures.rkt"
         "def-gen.rkt")

(define-syntax (def stx)

  (syntax-parse stx
    [(_ o:id sig:hc
        (~optional (~seq #:refinements ref:ff ...)
                   #:defaults ([(ref 1) null]))
        (~optional (~seq #:volatile? volatile?:boolean)
                   #:defaults ([volatile? #'#f]))
        (~optional (~seq #:lift-concrete? lift?:boolean)
                   #:defaults ([lift? #'#t])))

     (check-shape-ok #'o #'sig (syntax->list #'(ref ...)))
     (define max-inits
       (let go ([c #'sig])
         (syntax-parse c
           [((~literal ->) c ... _) (syntax-length #'(c ...))]
           [((~literal ->*) c ... #:rest _ _) (syntax-length #'(c ...))]
           [((~literal case->) clauses ...)
            (apply max 0 (map
                          (syntax-parser
                            [((~literal ->) c ... #:rest _ _) (syntax-length #'(c ...))]
                            [((~literal ->) c ... _) (syntax-length #'(c ...))])
                          (syntax->list #'(clauses ...))))]
           [((~literal ∀/c) _ c) (go #'c)])))
     (define/with-syntax defn-o
       #`(define (.o ℓ Ws $ Γ ⟪ℋ⟫ Σ ⟦k⟧)
           #,@(parameterize ([-o #'o]
                             [-ℓ #'ℓ]
                             [-Ws #'Ws]
                             [-$ #'$]
                             [-Γ #'Γ]
                             [-⟪ℋ⟫ #'⟪ℋ⟫]
                             [-Σ #'Σ]
                             [-⟦k⟧ #'⟦k⟧]
                             [-sig #'sig]
                             [-Wⁿ (gen-ids #'Ws 'W max-inits)]
                             [-Wᵣ (format-id #'Ws "Wᵣ")]
                             [-gen-lift? (syntax-e #'lift?)]
                             [-refinements (syntax->list #'(ref ...))])
                (gen-cases))))

     (pretty-write (syntax->datum #'defn-o))

     (hack:make-available #'o prim-table debug-table set-range! update-arity! add-const!)
     #`(begin
         (: .o : -⟦f⟧)
         defn-o
         (hash-set! debug-table 'o '#,(syntax->datum #'defn-o)))]))
