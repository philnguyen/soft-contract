#lang typed/racket/base

(require racket/match
         racket/contract
         racket/bool
         racket/string
         racket/math
         racket/list
         racket/stream
         racket/dict
         racket/function
         racket/set
         racket/flonum
         racket/fixnum
         racket/extflonum
         racket/generator
         racket/random
         racket/format
         racket/splicing
         typed/racket/unit
         syntax/parse/define
         set-extras
         "../utils/debug.rkt"
         (except-in "../ast/definition.rkt" normalize-arity arity-includes?)
         "../ast/shorthands.rkt"
         "../runtime/signatures.rkt"
         "../reduction/signatures.rkt"
         "../signatures.rkt"
         "signatures.rkt"
         "def-prim.rkt"
         (for-syntax racket/base
                     racket/syntax
                     syntax/parse))

(provide prims-04-09@)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;; 4.9 Pairs and Lists
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define-unit prims-04-09@
  (import prim-runtime^ proof-system^ widening^ kont^ app^ val^ pc^ sto^)
  (export)


  ;; 4.9.1 Constructors and Selectors

  (def-pred null?)
  (def-alias-internal cons? -cons?)
  (def-alias-internal cons -cons)
  (def-alias-internal car -car)
  (def-alias-internal cdr -cdr)
  (def-alias-internal set-mcdr! -set-cdr!) ;; HACK for running some Scheme programs
  (def-const null)
  (def-prim list? (any/c . -> . boolean?))
  (def-prim/custom (list ⟪ℋ⟫ ℒ Σ Γ Ws)
    (match Ws
      ['() {set (-ΓA (-Γ-facts Γ) (+W (list -null)))}]
      [_
       (define αₕ (-α->⟪α⟫ (-α.fld -𝒾-cons ℒ ⟪ℋ⟫ 0)))
       (define αₜ (-α->⟪α⟫ (-α.fld -𝒾-cons ℒ ⟪ℋ⟫ 1)))
       (for ([Wᵢ (in-list Ws)])
         (σ⊕! Σ Γ αₕ Wᵢ))
       (define Vₚ (-Cons αₕ αₜ))
       (σ⊕V! Σ αₜ -null)
       (σ⊕V! Σ αₜ Vₚ)
       (define tₚ (foldr (λ ([Wₗ : -W¹] [tᵣ : -?t]) (?t@ -cons (-W¹-t Wₗ) tᵣ)) -null Ws))
       {set (-ΓA (-Γ-facts Γ) (-W (list Vₚ) tₚ))}]))
  (def-prim/todo list* ; FIXME
    (-> list?))
  ; [HO] build-list

  ;; 4.9.2 List Operations
  (def-prim length (list? . -> . exact-nonnegative-integer?))
  (def-prim/todo list-ref
    (pair? exact-nonnegative-integer? . -> . any/c))
  (def-prim/custom (list-tail ⟪ℋ⟫ ℒ Σ Γ Ws)
    #:domain ([Wₗ any/c] [Wₙ exact-nonnegative-integer?])
    (define σ (-Σ-σ Σ))
    (match-define (-W¹ Vₗ sₗ) Wₗ)
    (match-define (-W¹ _  sₙ) Wₙ)
    (define sₐ (?t@ 'list-tail sₗ sₙ))
    (match Vₗ
      [(? -St? Vₗ)
       (define Vₕs (extract-list-content σ Vₗ))
       (define αₕ (-α->⟪α⟫ (-α.fld -𝒾-cons ℒ ⟪ℋ⟫ 0)))
       (define αₜ (-α->⟪α⟫ (-α.fld -𝒾-cons ℒ ⟪ℋ⟫ 1)))
       (define Vₜ (-Cons αₕ αₜ))
       (for ([Vₕ Vₕs]) (σ⊕V! Σ αₕ Vₕ))
       (σ⊕V! Σ αₜ Vₜ)
       (σ⊕V! Σ αₜ -null)
       {set (-ΓA (-Γ-facts Γ) (-W (list -null) sₐ))
            (-ΓA (-Γ-facts Γ) (-W (list Vₜ) sₐ))}]
      [(-b (list))
       {set (-ΓA (-Γ-facts Γ) (-W (list -null) sₐ))}]
      [_
       {set (-ΓA (-Γ-facts Γ) (-W (list (+● 'list?)) sₐ))}]))
  (def-prim append (() #:rest (listof list?) . ->* . list?))
  #;(def-prim/custom (append ⟪ℋ⟫ ℓ Σ Γ Ws) ; FIXME uses
      #:domain ([W₁ list?] [W₂ list?])
      (define σ (-Σ-σ Σ))
      (match-define (-W¹ V₁ s₁) W₁)
      (match-define (-W¹ V₂ s₂) W₂)
      (define sₐ (?t@ 'append s₁ s₂))
      (define Vₐ
        (match* (V₁ V₂)
          [((-b null) V₂) V₂]
          [((-Cons αₕ αₜ) V₂)
           (define ℒ (-ℒ ∅eq ℓ))
           (define αₕ* (-α->⟪α⟫ (-α.fld -𝒾-cons ℒ ⟪ℋ⟫ 0)))
           (define αₜ* (-α->⟪α⟫ (-α.fld -𝒾-cons ℒ ⟪ℋ⟫ 1)))
           (for ([Vₕ (σ@ σ αₕ)]) (σ⊕! Σ αₕ* Vₕ))
           (define Vₜs (set-add (σ@ σ αₜ) V₂))
           (for ([Vₜ* Vₜs]) (σ⊕! Σ αₜ* Vₜ*))
           (-Cons αₕ* αₜ*)]
          [(_ _) (-● {set 'list?})]))
      {set (-ΓA Γ (-W (list Vₐ) sₐ))})
  (def-prim/custom (reverse ⟪ℋ⟫ ℒ Σ Γ Ws)
    #:domain ([Wₗ list?])
    (define σ (-Σ-σ Σ))
    (match-define (-W¹ Vₗ sₗ) Wₗ)
    (define sₐ (?t@ 'reverse sₗ))
    (match Vₗ
      [(-b (list)) {set (-ΓA (-Γ-facts Γ) (-W (list -null) sₐ))}]
      [(-Cons _ _)
       (define αₕ (-α->⟪α⟫ (-α.fld -𝒾-cons ℒ ⟪ℋ⟫ 0)))
       (define αₜ (-α->⟪α⟫ (-α.fld -𝒾-cons ℒ ⟪ℋ⟫ 1)))
       (define Vₜ (-Cons αₕ αₜ))
       (for ([Vₕ (extract-list-content σ Vₗ)]) (σ⊕V! Σ αₕ Vₕ))
       (σ⊕V! Σ αₜ Vₜ)
       (σ⊕V! Σ αₜ -null)
       {set (-ΓA (-Γ-facts Γ) (-W (list Vₜ) sₐ))}]
      [(-● ps)
       (cond [(∋ ps -cons?) {set (-ΓA (-Γ-facts Γ) (-W (list (+● -cons?)) sₐ))}]
             [else          {set (-ΓA (-Γ-facts Γ) (-W (list (+● 'list?)) sₐ))}])]
      [_ {set (-ΓA (-Γ-facts Γ) (-W (list (+● 'list?)) sₐ))}]))

  ;; 4.9.3 List Iteration
  (def-ext (map $ ℒ Ws Γ ⟪ℋ⟫ Σ ⟦k⟧)
    ; FIXME uses 
    #:domain ([Wₚ (any/c . -> . any/c)]
              [Wₗ list?])
    (match-define (-Σ σ _ M) Σ)
    (match-define (-W¹ Vₚ sₚ) Wₚ)
    (match-define (-W¹ Vₗ sₗ) Wₗ)
    (define tₐ (?t@ 'map sₚ sₗ))
    (match Vₗ
      [(-b '()) (⟦k⟧ (-W (list -null) tₐ) $ Γ ⟪ℋ⟫ Σ)]
      [(-Cons _ _)
       (define ⟦k⟧* (mk-listof∷ tₐ ℒ ⟪ℋ⟫ ⟦k⟧))
       (for/union : (℘ -ς) ([V (extract-list-content σ Vₗ)])
                  (app $ ℒ Wₚ (list (-W¹ V #f)) Γ ⟪ℋ⟫ Σ ⟦k⟧*))]
      [_ (⟦k⟧ (-W (list (+● 'list?)) tₐ) $ Γ ⟪ℋ⟫ Σ)]))
  #;(def-prims (andmap ormap) ; FIXME uses
      (procedure? list . -> . any/c))
  (def-ext (for-each $ ℒ Ws Γ ⟪ℋ⟫ Σ ⟦k⟧)
    #:domain ([Wₚ (any/c . -> . any/c)]
              [Wₗ list?])
    #:result (list -void))
  #;(def-prims (foldl foldr) ; FIXME uses
      (procedure? any/c list? . -> . any/c))

  ;; 4.9.4 List Filtering
  (def-prim/todo filter
    ((any/c . -> . any/c) list? . -> . list?))
  (def-prim/todo remove ; FIXME uses
    (any/c list? . -> . list?))
  (def-prims (remq remv)
    (any/c list? . -> . list?))
  (def-prim/todo remove* ; FIXME uses
    (list? list? . -> . list?))
  (def-prims (remq* remv*)
    (list? list? . -> . list?))
  (def-prim/todo sort ; FIXME uses
    (list? (any/c any/c . -> . any/c) . -> . list?))

  ;; 4.9.5 List Searching
  (def-prim/custom (member ⟪ℋ⟫ ℒ Σ Γ Ws) ; FIXME uses
    #:domain ([Wₓ any/c] [Wₗ list?])
    (implement-mem 'member ⟪ℋ⟫ ℒ Σ Γ Wₓ Wₗ))
  (def-prim/custom (memv ⟪ℋ⟫ ℒ Σ Γ Ws)
    #:domain ([Wₓ any/c] [Wₗ list?])
    (implement-mem 'memv ⟪ℋ⟫ ℒ Σ Γ Wₓ Wₗ))
  (def-prim/custom (memq ⟪ℋ⟫ ℒ Σ Γ Ws)
    #:domain ([Wₓ any/c] [Wₗ list?])
    (implement-mem 'memq ⟪ℋ⟫ ℒ Σ Γ Wₓ Wₗ))
  (def-prim/todo memf ; TODO why doc only requires `procedure?` and not `arity-includes 1`
    (procedure? list? . -> . (or/c list? not)))
  (def-prim/todo findf
    (procedure? list? . -> . any/c))
  (def-prim assoc (any/c (listof pair?) . -> . (or/c pair? not))) ; FIXME uses ; FIXME listof
  (def-prims (assv assq) ; FIXME listof
    (any/c (listof pair?) . -> . (or/c pair? not)))
  (def-prim/todo assf ; TODO why doc only requires `procedure?`
    (procedure? list? . -> . (or/c pair? not)))

  ;; 4.9.6 Pair Acesssor Shorthands
  ; FIXME these are *opaque* for now. Make them composition of accessors
  (def-prims (caar cdar)
    ((cons/c pair? any/c) . -> . any/c))
  (def-prims (cadr cddr)
    ((cons/c any/c pair?) . -> . any/c))
  (def-prim caaar
    ((cons/c (cons/c pair? any/c) any/c) . -> . any/c))
  (def-prim caadr
    ((cons/c any/c (cons/c pair? any/c)) . -> . any/c))
  (def-prim cadar
    ((cons/c (cons/c any/c pair?) any/c) . -> . any/c))
  (def-prim caddr
    ((cons/c any/c (cons/c any/c pair?)) . -> . any/c))
  (def-prim cdaar
    ((cons/c (cons/c pair? any/c) any/c) . -> . any/c))
  (def-prim cdadr
    ((cons/c any/c (cons/c pair? any/c)) . -> . any/c))
  (def-prim cddar
    ((cons/c (cons/c any/c pair?) any/c) . -> . any/c))
  (def-prim cdddr
    ((cons/c any/c (cons/c any/c pair?)) . -> . any/c))
  ; TODO rest of them

  ;; 4.9.7 Additional List Functions and Synonyms
  (def-alias empty null)
  (def-alias pair? cons?)
  (def-alias empty? null?)
  (def-prim first
    ((cons/c any/c list?) . -> . any/c))
  (def-prim rest
    ((cons/c any/c list?) . -> . any/c))
  (def-prim second
    ((cons/c any/c (cons/c any/c list?)) . -> . any/c))
  (def-prim third
    ((cons/c any/c (cons/c any/c (cons/c any/c list?))) . -> . any/c))
  (def-prim fourth
    ((cons/c any/c (cons/c any/c (cons/c any/c (cons/c any/c list?)))) . -> . any/c))
  (def-prim fifth
    ((cons/c any/c (cons/c any/c (cons/c any/c (cons/c any/c (cons/c any/c list?))))) . -> . any/c))
  (def-prim sixth
    ((cons/c any/c (cons/c any/c (cons/c any/c (cons/c any/c (cons/c any/c (cons/c any/c list?)))))) . -> . any/c))
  (def-prim seventh
    ((cons/c any/c (cons/c any/c (cons/c any/c (cons/c any/c (cons/c any/c (cons/c any/c (cons/c any/c list?))))))) . -> . any/c))
  (def-prim eighth
    ((cons/c any/c (cons/c any/c (cons/c any/c (cons/c any/c (cons/c any/c (cons/c any/c (cons/c any/c (cons/c any/c list?)))))))) . -> . any/c))
  (def-prim ninth
    ((cons/c any/c (cons/c any/c (cons/c any/c (cons/c any/c (cons/c any/c (cons/c any/c (cons/c any/c (cons/c any/c (cons/c any/c list?))))))))) . -> . any/c))
  (def-prim tenth
    ((cons/c any/c (cons/c any/c (cons/c any/c (cons/c any/c (cons/c any/c (cons/c any/c (cons/c any/c (cons/c any/c (cons/c any/c (cons/c any/c list?)))))))))) . -> . any/c))
  (def-prim/todo last
    ((and/c list? (not/c empty?)) . -> . any/c))
  (def-prim/todo last-pair
    (pair? . -> . pair?))
  (def-prim/todo make-list
    (exact-nonnegative-integer? any/c . -> . list?))
  (def-prim/todo list-update ; FIXME range
    (list? exact-nonnegative-integer? (any/c . -> . any/c) . -> . list?))
  (def-prim/todo list-set ; FIXME range
    (list? exact-nonnegative-integer? any/c . -> . list?))
  (def-prim/todo take ; FIXME range
    (list? exact-nonnegative-integer? . -> . list?))
  (def-prim/todo drop
    (any/c exact-nonnegative-integer? . -> . any/c))
  #;[split-at ; FIXME
     (any/c exact-nonnegative-integer? . -> . (values list? any/c))]
  (def-prim/todo takef
    (any/c procedure? . -> . list?))
  (def-prim/todo dropf
    (any/c procedure? . -> . any/c))
  (def-prim/todo splitf-at ; FIXME
    (any/c procedure? . -> . (values list? any/c)))
  (def-prim/todo take-right
    (any/c exact-nonnegative-integer? . -> . any/c))
  (def-prim/todo drop-right
    (any/c exact-nonnegative-integer? . -> . list?))
  #;[split-at-right ; FIXME
     (any/c exact-nonnegative-integer? . -> . (values list? any/c))]
  (def-prim/todo takef-right
    (any/c procedure? . -> . list?))
  (def-prim/todo dropf-right
    (any/c procedure? . -> . any/c))
  #;[splitf-at-right ; FIXME uses
     (any/c procedure? . -> . (values list? any/c))]
  (def-prim list-prefix? ; FIXME uses
    (list? list? . -> . boolean?))
  (def-prim/todo take-common-prefix ; FIXME uses
    (list? list? . -> . list?))
  #;[drop-common-prefix ; FIXME uses
     (list? list? . -> . (values list? list?))]
  #;[split-common-prefix ; FIXME uses
     (list? list? . -> . (values list? list? list?))]
  (def-prim/todo add-between ; FIXME uses
    (list? any/c . -> . list?))
  #;[append* ; FIXME uses ; FIXME listof
     ((listof list?) . -> . list?)]
  (def-prim/todo flatten
    (any/c . -> . list?))
  (def-prim/todo check-duplicates ; FIXME uses
    (list? . -> . any/c)) ; simplified from doc's `(or/c any/c #f)`
  (def-prim/todo remove-duplicates ; FIXME uses
    (list? . -> . list?))
  (def-prim/todo filter-map ; FIXME uses
    (procedure? list? . -> . list?))
  (def-prim/todo count ; FIXME varargs
    (procedure? list? . -> . exact-nonnegative-integer?))
  #;[partition
     (procedure? list? . -> . (values list? list?))]
  (def-prim/todo range ; FIXME uses
    (real? . -> . list?))
  (def-prim/todo append-map ; FIXME varargs
    (procedure? list? . -> . list?))
  (def-prim/todo filter-not
    ((any/c . -> . any/c) list? . -> . list?))
  (def-prim/todo shuffle
    (list? . -> . list?))
  (def-prim/todo permutations
    (list? . -> . list?))
  (def-prim/todo in-permutations
    (list? . -> . sequence?))
  ; [HO] argmin argmax
  #;[group-by ; FIXME uses ; FIXME listof
     ((any/c . -> . any/c) list? . -> . (listof list?))]
  #;[cartesian-product ; FIXME varargs ; FIXME listof
     (() #:rest (listof list?) . ->* . (listof list?))]
  (def-prim/todo remf
    (procedure? list? . -> . list?))
  (def-prim/todo remf*
    (procedure? list? . -> . list?))

  ;; 4.9.8 Immutable Cyclic Data
  (def-prim/todo make-reader-graph
    (any/c . -> . any/c))
  (def-pred/todo placeholder?)
  (def-prim/todo make-placeholder
    (any/c . -> . placeholder?))
  (def-prim/todo placeholder-set!
    (placeholder? any/c . -> . void?))
  (def-prim/todo placeholder-get
    (placeholder? . -> . any/c))
  (def-pred/todo hash-placeholder?)
  #;[def-prims (make-hash-placeholder make-hasheq-placeholder make-hasheqv-placeholder) ; FIXME listof
      ((listof pair?) . -> . hash-placeholder?)]


  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
  ;;;;; HELPERS
  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (: implement-mem : Symbol -⟪ℋ⟫ -ℒ -Σ -Γ -W¹ -W¹ → (℘ -ΓA))
  (define (implement-mem o ⟪ℋ⟫ ℒ Σ Γ Wₓ Wₗ)

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
    
    (match-define (-W¹ Vₓ sₓ) Wₓ)
    (match-define (-W¹ Vₗ sₗ) Wₗ)
    (define sₐ (?t@ o sₓ sₗ))
    (define σ (-Σ-σ Σ))
    (match Vₗ
      [(-Cons _ _)
       (cond
         [(definitely-not-member? σ Vₓ Vₗ)
          {set (-ΓA (-Γ-facts Γ) (-W (list -ff) sₐ))}]
         [else
          (define αₕ (-α->⟪α⟫ (-α.fld -𝒾-cons ℒ ⟪ℋ⟫ 0)))
          (define αₜ (-α->⟪α⟫ (-α.fld -𝒾-cons ℒ ⟪ℋ⟫ 1)))
          (define Vₜ (-Cons αₕ αₜ))
          (for ([Vₕ (extract-list-content σ Vₗ)])
            (σ⊕V! Σ αₕ Vₕ))
          (σ⊕V! Σ αₜ Vₜ)
          (σ⊕V! Σ αₜ -null)
          (define Ans {set (-ΓA (-Γ-facts Γ) (-W (list Vₜ) sₐ))})
          (cond [(definitely-member? σ Vₓ Vₗ) Ans]
                [else (set-add Ans (-ΓA (-Γ-facts Γ) (-W (list -ff) sₐ)))])])]
      [(-b '()) {set (-ΓA (-Γ-facts Γ) (-W (list -ff) sₐ))}]
      [_ {set (-ΓA (-Γ-facts Γ) (-W (list (+● 'list? -cons?)) sₐ))
              (-ΓA (-Γ-facts Γ) (-W (list -ff) sₐ))}]))
  )
