#lang typed/racket/base

(provide ap ↝.@ mon ↝.mon.c ↝.mon.v blm
         flat-chk ↝.fc ↝.fc.and/c ↝.fc.or/c ↝.fc.not/c ↝.fc.struct/c ↝.or/c
         ↝.let-values ↝.letrec-values)

(require racket/match
         racket/set
         (except-in racket/function arity-includes?)
         (except-in racket/list remove-duplicates)
         "../utils/main.rkt"
         "../ast/main.rkt"
         "../runtime/main.rkt"
         "../proof-relation/main.rkt"
         "../delta.rkt"
         "helpers.rkt"
         "continuation-if.rkt"
         "continuation-amb.rkt"
         "continuation-begin.rkt"
         "wrap.rkt")


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;; Application
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Apply value `Wₕ` to arguments `Wₓ`s, returning store widening, answers, and suspended computation
(define/memo (ap [l : Mon-Party] [ℓ : -ℓ] [Wₕ : -W¹] [Wₓs : (Listof -W¹)]) : -⟦e⟧

  (λ (M σ X ℒ₀)
    (match-define (-ℒ ρ₀ Γ₀ 𝒞₀) ℒ₀)

    ;; Different handlers depending on the type of `Wₕ`.
    ;; Lots of free variables from above.

    (: ap/β : -formals -⟦e⟧ -ρ -Γ → (Values -Δσ (℘ -ΓW) (℘ -ΓE) -ΔX (℘ -ℐ)))
    ;; Apply λ abstraction
    (define (ap/β xs ⟦e⟧ ρ Γ₁)
      (define 𝒞₁ (𝒞+ 𝒞₀ (cons ⟦e⟧ ℓ)))
      (define-values (δσ ρ₁)
        (match xs
          [(? list? xs)
           (for/fold ([δσ : -Δσ ⊥σ] [ρ : -ρ ρ])
                     ([x xs] [V Vₓs])
             (define α (-α.x x 𝒞₁))
             (values (⊔ δσ α V) (ρ+ ρ x α)))]
          [_ (error 'ap/β "TODO: varargs")]))
      (define ℬ₁ (-ℬ ⟦e⟧ (-ℒ ρ₁ Γ₁ 𝒞₁)))
      (define bnd
        (let* ([fvs
                ;; It is important to take *all* of the caller's inscope variables,
                ;; rather than the invoked lambda's free variables.
                ;; Due to `canonicalize`, a refinement inside the closure
                ;; may refer to a variable not (directly) in the callee's scope
                ;; FIXME: due to a temp. hack for top-level reference,
                ;; `sₕ` being `λ` doesn't neccessarily mean it's created in this block
                ;; but if that's the case, the λ won't have FVs
                (if (-λ? sₕ)
                    (set-subtract (list->seteq (hash-keys ρ₀))
                                  (list->seteq (assert xs list?)))
                    ∅eq)]
               [param->arg
                (for/hasheq : (HashTable Var-Name -φ) ([x (assert xs list?)] [sₓ sₓs] #:when sₓ)
                  (values x (e->φ sₓ)))]
               [mapping
                (for/fold ([mapping : (HashTable Var-Name -φ) param->arg]) ([x fvs])
                  (assert (not (hash-has-key? mapping x))) ; FIXME is this neccessary?
                  (hash-set mapping x (e->φ (canonicalize Γ₀ x))))])
          (-binding (s->φ sₕ) xs mapping)))
      (values δσ ∅ ∅ ∅ {set (-ℐ (-ℋ ℒ₀ bnd '□) ℬ₁)}))
    
    (with-debugging/off
      ((δσ ΓWs ΓEs δX ℐs)
       (match Vₕ
         
         ;; Struct operators cannot be handled by `δ`, because structs can be arbitrarily wrapped
         ;; by proxies, and contract checking is arbitrarily deep
         ;; Also, there's no need to check for preconditions, because they should have been caught
         ;; by wrapping contracts
         [(-st-p s)     (ap/st-p   s  )]
         [(-st-mk s)    (ap/st-mk  s  )]
         [(-st-ac  s i) (with-guarded-arity 1 (ap/st-ac  s i))]
         [(-st-mut s i) (with-guarded-arity 2 (ap/st-mut s i))]
         ['contract-first-order-passes? (ap/contract-first-order-passes?)]
         ['vector-ref  (ap/vector-ref )]
         ['vector-set! (ap/vector-set!)]
         ['unsafe-struct-ref (ap/unsafe-struct-ref)]
         ['unsafe-struct-set! (ap/unsafe-struct-set!)]
         
         ;; Regular stuff
         [(? symbol? o) (ap/δ o)]
         [(-Clo xs ⟦e⟧ ρ Γ)
          (with-guarded-arity (formals-arity xs)
            (ap/β xs ⟦e⟧ ρ Γ))]
         [(-Case-Clo clauses ρ Γ) #|DONE|#]
         [(-Ar C α l³) #|DONE|#]
         [(-And/C #t α₁ α₂) #|DONE|#]
         [(-Or/C #t α₁ α₂) #|DONE|#]
         [(-Not/C α) #|DONE|#]
         [(-St/C #t s αs) #|DONE|#]
         [(-● _)
          (case (MΓ⊢oW M Γ₀ 'procedure? Wₕ)
            [(✓ ?) (ap/●)]
            [(✗) (values ⊥σ ∅ {set (-ΓE Γ₀ (-blm l 'Λ (list 'procedure?) (list Vₕ)))} ∅ ∅)])]
         [_ (values ⊥σ ∅ {set (-ΓE Γ₀ (-blm l 'Λ (list 'procedure?) (list Vₕ)))} ∅ ∅)]))
      (printf "Ap: ~a ~a:~n" (show-W¹ Wₕ) (map show-W¹ Wₓs))
      (printf "answers:~n")
      (for ([A ΓWs]) (printf "  - ~a~n" (show-A A)))
      (printf "errors:~n")
      (for ([A ΓEs]) (printf "  - ~a~n" (show-A A)))
      (printf "pending:~n")
      (for ([ℐ  ℐs]) (printf "  - ~a~n" (show-ℐ ℐ)))
      (printf "~n"))))
