#lang typed/racket/base

;; This module provides facility for defining external library functions
;; Defining an external function through `def-ext` is different from treating it
;; as an opaque value wrapped in contract in several ways:
;; - There's support for cheating with custom definition for more precisions
;;   (e.g. `reverse` returns a list of the same dynamically determined "type"
;;   as its arguments)

(provide (all-defined-out))

(require (for-syntax racket/base
                     racket/match
                     racket/contract
                     racket/syntax
                     racket/pretty
                     syntax/parse
                     "../primitives/utils.rkt")
         racket/match
         racket/set
         racket/contract
         "../utils/map.rkt"
         "../utils/set.rkt"
         "../ast/definition.rkt"
         "../runtime/main.rkt"
         "../reduction/compile/app.rkt"
         "../proof-relation/main.rkt"
         "gen.rkt"
         "def-ext-runtime.rkt")

(begin-for-syntax

  (define/contract (gen-blm blm)
    (syntax? . -> . syntax?)
    #`(#,(-⟦k⟧) #,blm #,(-$) #,(-Γ) #,(-⟪ℋ⟫) #,(-Σ)))
)


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;; Main stuff
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define-syntax (def-ext stx)
  (define/contract (gen-defn o .o defn)
    (identifier? identifier? syntax? . -> . syntax?)
    #`(begin
        (: #,.o : -⟦f⟧)
        #,defn
        (hash-set! ext-table '#,o #,.o)
        (hash-set! debug-table '#,o '#,(syntax->datum defn))))
  
  (syntax-parse stx
    
    ;; Only declare contract, providing crudest approximation
    [(_ o:id c:hf)
     (define/syntax-parse (cₓ ...) (attribute c.init))
     (define/syntax-parse d (attribute c.rng))
     (define/with-syntax (W ...) (gen-ids #'o 'W (length (syntax->list #'(cₓ ...)))))
     #`(def-ext (o $ ℒ Ws Γ ⟪ℋ⟫ Σ ⟦k⟧)
         #:domain ([W cₓ] ...)
         (match-define (-Σ σ σₖ _) Σ)
         (define sₐ (-?@ 'o (-W¹-s W) ...))
         (define Wₐ (-W (list #,(parameterize ([-σ #'σ])
                                  (gen-wrap #'d #'-●.V #'sₐ)))
                        sₐ))
         (begin (add-leak! Σ (-W¹-V W)) ...)
         (define αₖ (-ℋ𝒱))
         (define κ (-κ (bgn0.e∷ Wₐ '() ⊥ρ ⟦k⟧) Γ ⟪ℋ⟫ 'void '()))
         (σₖ⊕! Σ αₖ κ)
         {set (-ς↑ αₖ Γ ⟪ℋ⟫)})]

    ;; Declaring simple result, skipping havoc-ing of arguments
    [(_ (o:id $:id ℒ:id Ws:id Γ:id ⟪ℋ⟫:id Σ:id ⟦k⟧:id)
        #:domain ([W:id c:hc] ...)
        #:result e)
     #'(def-ext (o $ ℒ Ws Γ ⟪ℋ⟫ Σ ⟦k⟧)
         #:domain ([W c] ...)
         (define sₐ (apply -?@ 'o (map -W¹-s Ws)))
         (⟦k⟧ (-W e sₐ) $ Γ ⟪ℋ⟫ Σ))]

    ;; Custom modes for hacking
    [(_ (o:id $:id ℒ:id Ws:id Γ:id ⟪ℋ⟫:id Σ:id ⟦k⟧:id)
        #:domain ([W:id c:hc] ...)
        e:expr ...)
     (define n (length (syntax->list #'(W ...))))
     (define/with-syntax .o (prefix-id #'o))
     (define defn-o
       #`(define (.o $ ℒ Ws Γ ⟪ℋ⟫ Σ ⟦k⟧)
           (define ℓ (-ℒ-app ℒ))
           #,@(parameterize ([-o #'o]
                             [-⟪ℋ⟫ #'⟪ℋ⟫]
                             [-ℒ #'ℒ]
                             [-ℓ #'ℓ]
                             [-Σ #'Σ]
                             [-σ #'σ]
                             [-M #'M]
                             [-Γ #'Γ]
                             [-⟦k⟧ #'⟦k⟧]
                             [-$ #'$]
                             [-Ws #'Ws]
                             [-Wₙ (syntax->list #'(W ...))]
                             [-sₙ (gen-ids #'s 's n)]
                             [-bₙ (gen-ids #'b 'b n)]
                             [-W* (format-id #'W* "W*")]
                             [-b* (format-id #'b* "b*")]
                             [-s* (format-id #'s* "s*")]
                             [-sig #'(-> c ... any/c)]
                             [-gen-blm gen-blm])
                (gen-arity-check n
                 (gen-precond-checks
                  (gen-arg-wraps
                   (syntax->list #'(e ...))))))))
     ;(pretty-write (syntax->datum defn-o))
     (gen-defn #'o #'.o defn-o)]
    
    ;; Skipping precondition checks
    [(_ (o:id $:id ℒ:id Ws:id Γ:id ⟪ℋ⟫:id Σ:id ⟦k⟧:id) e:expr ...)
     (define/with-syntax .o (prefix-id #'o))
     (define defn-o #`(define (.o $ ℒ Ws Γ ⟪ℋ⟫ Σ ⟦k⟧) e ...))
     (gen-defn #'o #'.o defn-o)]))
