#lang typed/racket/base

;; This module provides runtime support for the def-prim DSL

(provide (all-defined-out))
(require racket/match
         racket/set
         syntax/parse/define
         "../utils/main.rkt"
         "../ast/main.rkt"
         "../runtime/main.rkt"
         "../proof-relation/main.rkt")

(define-type -⟦o⟧ (-⟪ℋ⟫ ℓ -Σ -Γ (Listof -W¹) → (℘ -ΓA)))

(: unchecked-ac : -σ -Γ -st-ac -W¹ → (℘ -W¹))
;; unchecked struct accessor, assuming the value is already checked to be the right struct.
;; This is only for use internally, so it's safe (though imprecise) to ignore field wraps
(define (unchecked-ac σ Γ ac W)
  (define-set seen : ⟪α⟫ #:eq? #t #:as-mutable-hash? #t)
  (match-define (-W¹ V s) W)
  (match-define (-st-ac 𝒾 i) ac)
  (define φs (-Γ-facts Γ))
  (define s* (-?@ ac s))
  (let go ([V : -V V])
    (match V
      [(-St (== 𝒾) αs)
       (for/set: : (℘ -W¹) ([V* (in-set (σ@ σ (list-ref αs i)))]
                            #:when (plausible-V-s? φs V* s*))
         (-W¹ V* s*))]
      [(-St* (-St/C _ (== 𝒾) _) α _)
       (cond [(seen-has? α) ∅]
             [else
              (seen-add! α)
              (for/union : (℘ -W¹) ([V (in-set (σ@ σ α))]
                                    #:when (plausible-V-s? φs V s))
                (go V))])]
      [(? -●?) {set (-W¹ -●.V s*)}]
      [_ ∅])))

(: ⊢?/quick : -R -σ -Γ -o -W¹ * → Boolean)
;; Perform a relatively cheap check (i.e. no SMT call) if `(o W ...)` returns `R`
(define (⊢?/quick R σ Γ o . Ws)
  (define-values (Vs ss) (unzip-by -W¹-V -W¹-s Ws))
  (eq? R (first-R (apply p∋Vs σ o Vs)
                  (Γ⊢e Γ (apply -?@ o ss)))))

(: implement-predicate : -M -σ -Γ Symbol (Listof -W¹) → (℘ -ΓA))
(define (implement-predicate M σ Γ o Ws)
  (define ss (map -W¹-s Ws))
  (define A
    (case (apply MΓ⊢oW M σ Γ o Ws)
      [(✓) -tt.Vs]
      [(✗) -ff.Vs]
      [(?) -Bool.Vs]))
  {set (-ΓA Γ (-W A (apply -?@ o ss)))})

(define/memoeq (total-pred [n : Index]) : (Symbol → -⟦o⟧)
  (λ (o)
    (λ (⟪ℋ⟫ ℓ Σ Γ Ws)
      (cond [(equal? n (length Ws))
             (match-define (-Σ σ _ M) Σ)
             (implement-predicate M σ Γ o Ws)]
            [else
             {set (-ΓA Γ (blm-arity ℓ o n (map -W¹-V Ws)))}]))))

(define alias-table : (HashTable Symbol Symbol) (make-hasheq))
(define alias-internal-table : (HashTable Symbol (U -st-mk -st-p -st-ac -st-mut)) (make-hasheq))
(define const-table : (HashTable Symbol -b) (make-hasheq))
(define prim-table  : (HashTable Symbol -⟦o⟧) (make-hasheq))
(define opq-table   : (HashTable Symbol -●) (make-hasheq))
(define debug-table : (HashTable Symbol Any) (make-hasheq))

(: get-prim : Symbol → (Option -⟦o⟧))
(define (get-prim o) (hash-ref prim-table o #f))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;; Helpers for some of the primitives
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(: implement-mem : Symbol -⟪ℋ⟫ ℓ -Σ -Γ -W¹ -W¹ → (℘ -ΓA))
(define (implement-mem o ⟪ℋ⟫ ℓ Σ Γ Wₓ Wₗ)
  (match-define (-W¹ Vₓ sₓ) Wₓ)
  (match-define (-W¹ Vₗ sₗ) Wₗ)
  (define sₐ (-?@ o sₓ sₗ))
  (define σ (-Σ-σ Σ))
  (match Vₗ
    [(-Cons _ _)
     (cond
       [(definitely-not-member? σ Vₓ Vₗ)
        {set (-ΓA Γ (-W -ff.Vs sₐ))}]
       [else
        (define ℒ (-ℒ ∅eq ℓ))
        (define αₕ (-α->⟪α⟫ (-α.fld -𝒾-cons ℒ ⟪ℋ⟫ 0)))
        (define αₜ (-α->⟪α⟫ (-α.fld -𝒾-cons ℒ ⟪ℋ⟫ 1)))
        (define Vₜ (-Cons αₕ αₜ))
        (for ([Vₕ (extract-list-content σ Vₗ)])
          (σ⊕V! Σ αₕ Vₕ))
        (σ⊕V*! Σ [αₜ ↦ Vₜ] [αₜ ↦ -null])
        (define Ans {set (-ΓA Γ (-W (list Vₜ) sₐ))})
        (cond [(definitely-member? σ Vₓ Vₗ) Ans]
              [else (set-add Ans (-ΓA Γ (-W -ff.Vs sₐ)))])])]
    [(-b '()) {set (-ΓA Γ (-W -ff.Vs sₐ))}]
    [_ {set (-ΓA Γ (-W (list (-● {set 'list? -cons?})) sₐ))
            (-ΓA Γ (-W -ff.Vs sₐ))}]))

(: definitely-member? : -σ -V -St → Boolean)
(define (definitely-member? σ V Vₗ)
  (let loop ([Vₗ : -V Vₗ] [seen : (℘ -V) ∅])
    (cond
      [(∋ seen Vₗ) #f]
      [else
       (match Vₗ
         [(-Cons αₕ αₜ)
          (or (for/and : Boolean ([Vₕ (σ@ σ αₕ)]) (definitely-equal? σ V Vₕ))
              (for/and : Boolean ([Vₜ (σ@ σ αₜ)]) (loop Vₜ (set-add seen Vₗ))))]
         [_ #f])])))

(: definitely-not-member? : -σ -V -St → Boolean)
(define (definitely-not-member? σ V Vₗ)
  (let loop ([Vₗ : -V Vₗ] [seen : (℘ -V) ∅])
    (cond
      [(∋ seen Vₗ) #t]
      [else
       (match Vₗ
         [(-Cons αₕ αₜ)
          (and (for/and : Boolean ([Vₕ (σ@ σ αₕ)]) (definitely-not-equal? σ V Vₕ))
               (for/and : Boolean ([Vₜ (σ@ σ αₜ)]) (loop Vₜ (set-add seen Vₗ))))]
         [(-b (list)) #t]
         [_ #f])])))


(: definitely-equal? : -σ -V -V → Boolean)
(define (definitely-equal? σ V₁ V₂)
  (let loop ([V₁ : -V V₁] [V₂ : -V V₂] [seen : (℘ (Pairof -V -V)) ∅])
    (cond
      [(∋ seen (cons V₁ V₂)) #t]
      [else
       (match* (V₁ V₂)
         [((-b b₁) (-b b₂)) (equal? b₁ b₂)]
         [((-St 𝒾 αs₁) (-St 𝒾 αs₂))
          (for/and : Boolean ([α₁ : ⟪α⟫ αs₁] [α₂ : ⟪α⟫ αs₂])
            (define Vs₁ (σ@ σ α₁))
            (define Vs₂ (σ@ σ α₂))
            (for/and : Boolean ([V₁* Vs₁]) ; can't use for*/and :(
              (for/and : Boolean ([V₂* Vs₂])
                (loop V₁* V₂* (set-add seen (cons V₁ V₂))))))]
         [(_ _) #f])])))

(: definitely-not-equal? : -σ -V -V → Boolean)
(define (definitely-not-equal? σ V₁ V₂)
  (let loop ([V₁ : -V V₁] [V₂ : -V V₂] [seen : (℘ (Pairof -V -V)) ∅])
    (cond
      [(∋ seen (cons V₁ V₂)) #t]
      [else
       (match* (V₁ V₂)
         [((-b b₁) (-b b₂)) (not (equal? b₁ b₂))]
         [((-St 𝒾₁ αs₁) (-St 𝒾₂ αs₂))
          (or (not (equal? 𝒾₁ 𝒾₂))
              (for/or : Boolean ([α₁ : ⟪α⟫ αs₁] [α₂ : ⟪α⟫ αs₂])
                (define Vs₁ (σ@ σ α₁))
                (define Vs₂ (σ@ σ α₂))
                (for/and : Boolean ([V₁ Vs₁])
                  (for/and : Boolean ([V₂ Vs₂])
                    (loop V₁ V₂ (set-add seen (cons V₁ V₂)))))))]
         [(_ _) #f])])))

(: list-of-non-null-chars? : -σ -V → Boolean)
;; Check if a value is definitely a list of non-null characters
(define (list-of-non-null-chars? σ V)
  (define-set seen : ⟪α⟫ #:eq? #t #:as-mutable-hash? #t)
  (with-debugging/off ((ans) (let go : Boolean ([V : -V V])
                                  (match V
                                    [(-b (list)) #t]
                                    [(-Cons αₕ αₜ)
                                     (and (for/and : Boolean ([Vₕ (σ@ σ αₕ)])
                                            (equal? '✗ (p∋Vs σ 'equal? (-b #\null) Vₕ)))
                                          (or
                                           (seen-has? αₜ)
                                           (begin
                                             (seen-add! αₜ)
                                             (for/and : Boolean ([Vₜ (σ@ σ αₜ)])
                                               (go Vₜ)))))]
                                    [_ #f])))
    (printf "list-of-non-null-char? ~a -> ~a~n"
            (show-V V) ans)
    (for ([(α Vs) (span-σ (-σ-m σ) (V->⟪α⟫s V))])
      (printf "  - ~a ↦ ~a~n" (show-⟪α⟫ (cast α ⟪α⟫)) (set-map Vs show-V)))
    (printf "~n")))

(: with-MΓ⊢oW-handler (∀ (X) (-Γ → (℘ X)) (-Γ → (℘ X)) -M -σ -Γ -o -W¹ * → (℘ X)))
(define (with-MΓ⊢oW-handler f₁ f₂ M σ Γ o . Ws)
  (define ss (map -W¹-s Ws))
  (case (apply MΓ⊢oW M σ Γ o Ws)
    [(✓) (f₁ Γ)]
    [(✗) (f₂ Γ)]
    [(?) (∪ (f₁ (Γ+ Γ (apply -?@ o ss)))
            (f₂ (Γ+ Γ (-?@ 'not (apply -?@ o ss)))))]))

(define-simple-macro (with-MΓ⊢oW (M:expr σ:expr Γ:expr o:expr W:expr ...) #:on-t on-t:expr #:on-f on-f:expr)
  (with-MΓ⊢oW-handler on-t on-f M σ Γ o W ...))

(: with-MΓ⊢oW-callback (∀ (X) (→ (℘ X)) (→ (℘ X)) -M -σ -Γ -o -W¹ * → (℘ X)))
(define (with-MΓ⊢oW-callback on-t on-f M σ Γ o . Ws)
  (case (apply MΓ⊢oW M σ Γ o Ws)
    [(✓) (on-t)]
    [(✗) (on-f)]
    [(?) (∪ (on-t) (on-f))]))

(define-simple-macro (with-MΓ⊢oW/no-refine (M:expr σ:expr Γ:expr o:expr W:expr ...) #:on-t on-t:expr #:on-f on-f:expr)
  (with-MΓ⊢oW-callback on-t on-f M σ Γ o W ...))

(: with-p∋Vs-handler (∀ (X) (→ (℘ X)) (→ (℘ X)) -σ -o -V * → (℘ X)))
(define (with-p∋Vs-handler t f σ o . Vs)
  (case (apply p∋Vs σ o Vs)
    [(✓) (t)]
    [(✗) (f)]
    [(?) (∪ (t) (f))]))

(define-simple-macro (with-p∋Vs (σ:expr o:expr V:expr ...) #:on-t t:expr #:on-f f:expr)
  (with-p∋Vs-handler t f σ o V ...))

(: with-arity-check-handler (∀ (X) -Γ -W¹ Arity (-Γ → (℘ X)) (-Γ → (℘ X)) → (℘ X)))
(define (with-arity-check-handler Γ W arity t f)
  (match-define (-W¹ V s) W) ; ignore `Γ` and `s` for now
  (define (on-t) (t Γ)) ; TODO
  (define (on-f) (f Γ)) ; TODO
  (cond [(V-arity V) =>
         (λ ([a : Arity])
           ((if (arity-includes? a arity) t f) Γ))]
        [else (∪ (t Γ) (f Γ))]))

(define-simple-macro (with-arity-check (Γ:expr W:expr a:expr) #:on-t t:expr #:on-f f:expr)
  (with-arity-check-handler Γ W a t f))

(: ss->bs : (Listof -s) → (Option (Listof Base)))
(define (ss->bs ss)
  (foldr (λ ([s : -s] [?bs : (Option (Listof Base))])
           (and ?bs (-b? s) (cons (-b-unboxed s) ?bs)))
         '()
         ss))

(: vec-len : -σ -Γ -W¹ → -W¹)
(define (vec-len σ Γ W)
  (match-define (-W¹ V s) W)
  (define ?n : (Option Natural)
    (match V
      [(-Vector ⟪α⟫s) (length ⟪α⟫s)]
      [(-Vector^ _ V)
       (match V
         [(-b (? exact-nonnegative-integer? n)) n]
         [_ #f])]
      [(-Vector/guard grd _ _)
       (match grd
         [(-Vector/C ⟪α⟫s) (length ⟪α⟫s)]
         [_ #f])]
      [_ #f]))
  (define Vₙ (if ?n (-b ?n) -●.V))
  (-W¹ Vₙ (-?@ 'vector-length s)))
