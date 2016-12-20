#lang typed/racket/base

;; This module provides runtime support for the def-prim DSL

(provide (all-defined-out))
(require racket/match
         racket/set
         syntax/parse/define
         "../utils/main.rkt"
         "../ast/definition.rkt"
         "../runtime/main.rkt"
         "../proof-relation/main.rkt")

(define-type -⟦o⟧! (-⟪ℋ⟫ -ℓ -l -Σ -Γ (Listof -W¹) → (℘ -ΓA)))
(define-type Prim-Thunk (-Γ → (℘ -ΓA)))

(: unchecked-ac : -σ -Γ -st-ac -W¹ → (℘ -W¹))
;; unchecked struct accessor, assuming the value is already checked to be the right struct.
;; This is only for use internally, so it's safe (though imprecise) to ignore field wraps
(define (unchecked-ac σ Γ ac W)
  (define-set seen : -⟪α⟫ #:eq? #t #:as-mutable-hash? #t)
  (match-define (-W¹ (list V) s) W)
  (match-define (-st-ac 𝒾 i) ac)
  (define φs (-Γ-facts Γ))
  (define s* (-?@ ac s))
  (let go ([V : -V V])
    (match V
      [(-St (== 𝒾) αs)
       (for/set: : (℘ -W¹) ([V* (in-set (σ@ σ (list-ref αs i)))]
                            #:when (plausible-V-s? φs V* s*))
         (-W¹ V* s*))]
      [(-St* (== 𝒾) _ α _)
       (cond [(seen-has? α) ∅]
             [else
              (seen-add! α)
              (for/union : (℘ -W¹) ([V (in-set (σ@ σ α))]
                                    #:when (plausible-V-s? φs V s))
                (go V))])]
      [(? -●?) {set (-W¹ -●/V s*)}]
      [_ ∅])))

(: ⊢?/quick : -R -σ -Γ -o -W¹ * → Boolean)
;; Perform a relatively cheap check (i.e. no SMT call) if `(o W ...)` returns `R`
(define (⊢?/quick R σ Γ o . Ws)
  (define-values (Vs ss) (unzip-by -W¹-V -W¹-s Ws))
  (eq? R (first-R (apply p∋Vs σ o Vs)
                  (Γ⊢e Γ (apply -?@ o ss)))))

(: blm : -Γ -l -l (U -V -v) (U -W¹ -V) → (℘ -ΓA))
(define (blm Γ who whom why what)
  (define what* (if (-W¹? what) (-W¹-V what) what))
  {set (-ΓA Γ (-blm who whom (list why) (list what*)))})

(: implement-predicate : -M -σ -Γ Symbol (Listof -W¹) → (℘ -ΓA))
(define (implement-predicate M σ Γ o Ws)
  (define ss (map -W¹-s Ws))
  (define A
    (case (apply MΓ⊢oW M σ Γ o Ws)
      [(✓) -True/Vs]
      [(✗) -False/Vs]
      [(?) -Bool/Vs]))
  {set (-ΓA Γ (-W A (apply -?@ o ss)))})

(define/memoeq (total-pred [n : Index]) : (Symbol → -⟦o⟧!)
  (λ (o)
    (λ (⟪ℋ⟫ ℓ l Σ Γ Ws)
      (cond [(equal? n (length Ws))
             (match-define (-Σ σ _ M) Σ)
             (implement-predicate M σ Γ o Ws)]
            [else
             {set (-ΓA Γ (blm-arity l o n (map -W¹-V Ws)))}]))))

(define alias-table : (HashTable Symbol Symbol) (make-hasheq))
(define alias-internal-table : (HashTable Symbol (U -st-mk -st-p -st-ac -st-mut)) (make-hasheq))
(define const-table : (HashTable Symbol -b) (make-hasheq))
(define prim-table  : (HashTable Symbol -⟦o⟧!) (make-hasheq))
(define opq-table   : (HashTable Symbol -●) (make-hasheq))
(define debug-table : (HashTable Symbol Any) (make-hasheq))

(define (get-defined-prim-names)
  ;; TODO def-opq table
  (∪ (list->seteq (hash-keys const-table))
     (list->seteq (hash-keys prim-table))
     (list->seteq (hash-keys alias-table))
     (list->seteq (hash-keys alias-internal-table))))

;; range can't be:
;;  - `Syntaxof Any`, b/c can't convert to contract
;;  - `Any`, because TR doens't know how to wrap it
(: get-prim-parse-result : Symbol → (Values (U 'quote 'const) Symbol))
(define (get-prim-parse-result name)
  (cond [(hash-has-key? prim-table name) (values 'quote name)]
        [(hash-has-key? const-table name) (values 'const name)]
        [(hash-ref alias-table name #f) => get-prim-parse-result]
        [(hash-has-key? alias-internal-table name) (values 'const name)]
        [(hash-ref opq-table name #f) =>
         (λ ([V : -V])
           (error 'get-prim "TODO: opq-table"))]
        [else (error 'get-prim-parse-result "~a" name)]))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;; Helpers for some of the primitives
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(: implement-mem : Symbol -⟪ℋ⟫ -ℓ -Σ -Γ -W¹ -W¹ → (℘ -ΓA))
(define (implement-mem o ⟪ℋ⟫ ℓ Σ Γ Wₓ Wₗ)
  (define σ (-Σ-σ Σ))
  (match-define (-W¹ Vₓ sₓ) Wₓ)
  (match-define (-W¹ Vₗ sₗ) Wₗ)
  (define sₐ (-?@ o sₓ sₗ))
  (match Vₗ
    [(-Cons _ _)
     (cond
       [(definitely-not-member? σ Vₓ Vₗ)
        {set (-ΓA Γ (-W -False/Vs sₐ))}]
       [else
        (define ℒ (-ℒ ∅ ℓ))
        (define αₕ (-α->-⟪α⟫ (-α.fld -𝒾-cons ℒ ⟪ℋ⟫ 0)))
        (define αₜ (-α->-⟪α⟫ (-α.fld -𝒾-cons ℒ ⟪ℋ⟫ 1)))
        (define Vₜ (-Cons αₕ αₜ))
        (for ([Vₕ (extract-list-content σ Vₗ)])
          (σ⊕! σ αₕ Vₕ))
        (σ⊕*! σ [αₜ ↦ Vₜ] [αₜ ↦ -null])
        (define Ans {set (-ΓA Γ (-W (list Vₜ) sₐ))})
        (cond [(definitely-member? σ Vₓ Vₗ) Ans]
              [else (set-add Ans (-ΓA Γ (-W -False/Vs sₐ)))])])]
    [(-b '()) {set (-ΓA Γ (-W -False/Vs sₐ))}]
    [_ {set (-ΓA Γ (-W (list (-● {set 'list? -cons?})) sₐ))
            (-ΓA Γ (-W -False/Vs sₐ))}]))

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
          (for/and : Boolean ([α₁ : -⟪α⟫ αs₁] [α₂ : -⟪α⟫ αs₂])
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
              (for/or : Boolean ([α₁ : -⟪α⟫ αs₁] [α₂ : -⟪α⟫ αs₂])
                (define Vs₁ (σ@ σ α₁))
                (define Vs₂ (σ@ σ α₂))
                (for/and : Boolean ([V₁ Vs₁])
                  (for/and : Boolean ([V₂ Vs₂])
                    (loop V₁ V₂ (set-add seen (cons V₁ V₂)))))))]
         [(_ _) #f])])))

(: list-of-non-null-chars? : -σ -V → Boolean)
;; Check if a value is definitely a list of non-null characters
(define (list-of-non-null-chars? σ V)
  (define-set seen : -⟪α⟫ #:eq? #t #:as-mutable-hash? #t)
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
    (for ([(α Vs) (hash-copy/spanning* (-σ-m σ) (V->⟪α⟫s V) V->⟪α⟫s)])
      (printf "  - ~a ↦ ~a~n" (show-⟪α⟫ (cast α -⟪α⟫)) (set-map Vs show-V)))
    (printf "~n")))

(: with-MΓ⊢oW-handler : (-Γ → (℘ -ΓA)) (-Γ → (℘ -ΓA)) -M -σ -Γ -o -W¹ * → (℘ -ΓA))
(define (with-MΓ⊢oW-handler f₁ f₂ M σ Γ o . Ws)
  (define ss (map -W¹-s Ws))
  (define (on-t) (f₁ (Γ+ Γ (apply -?@ o ss))))
  (define (on-f) (f₂ (Γ+ Γ (-?@ 'not (apply -?@ o ss)))))
  (case (apply MΓ⊢oW M σ Γ o Ws)
    [(✓) (on-t)]
    [(✗) (on-f)]
    [(?) (∪ (on-t) (on-f))]))

(: with-p∋Vs-handler : (→ (℘ -ΓA)) (→ (℘ -ΓA)) -σ -o -V * → (℘ -ΓA))
(define (with-p∋Vs-handler t f σ o . Vs)
  (case (apply p∋Vs σ o Vs)
    [(✓) (t)]
    [(✗) (f)]
    [(?) (∪ (t) (f))]))

(define-simple-macro (with-MΓ⊢oW (M:expr σ:expr Γ:expr o:expr W:expr ...) #:on-t on-t:expr #:on-f on-f:expr)
  (with-MΓ⊢oW-handler on-t on-f M σ Γ o W ...))

(define-simple-macro (with-p∋Vs (σ:expr o:expr V:expr ...) #:on-t t:expr #:on-f f:expr)
  (with-p∋Vs-handler t f σ o V ...))

(: ss->bs : (Listof -s) → (Option (Listof Base)))
(define (ss->bs ss)
  (foldr (λ ([s : -s] [?bs : (Option (Listof Base))])
           (and ?bs (-b? s) (cons (-b-unboxed s) ?bs)))
         '()
         ss))
