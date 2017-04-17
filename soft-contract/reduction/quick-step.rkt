#lang typed/racket/base

(provide run debug-trace? debug-iter?)

(require racket/set
         racket/match
         racket/list
         "../settings.rkt"
         "../utils/main.rkt"
         "../ast/main.rkt"
         "../runtime/main.rkt"
         "../proof-relation/main.rkt" #;(only-in "../proof-relation/ext.rkt" miss/total)
         "compile/utils.rkt"
         "compile/kontinuation.rkt"
         "compile/main.rkt"
         "../externals/main.rkt" ; for side effects
         "havoc.rkt"
         )

(define-type Ctx (List -σ -σₖ -M))

(: run : -⟦e⟧ → (Values (℘ -ΓA) -Σ))
(define (run ⟦e⟧)
  (define seen : (HashTable -ς Ctx) (make-hash))
  (define αₖ₀ : -αₖ (-ℬ '() ⟦e⟧ ⊥ρ #;∅))
  (define Σ (-Σ ⊥σ (hash-set ⊥σₖ αₖ₀ ∅) ⊥M))
  (define root₀ ; all addresses to top-level definitions are conservatively active
    (for/fold ([root₀ : (℘ ⟪α⟫) ∅eq]) ([𝒾 (top-levels)])
      (set-add (set-add root₀ (-α->⟪α⟫ 𝒾)) (-α->⟪α⟫ (-α.wrp 𝒾)))))

  (define iter : Natural 0)

  (let loop! ([front : (℘ -ς) {set (-ς↑ αₖ₀ ⊤Γ ⟪ℋ⟫∅)}])
    (unless (or (set-empty? front) #|FIXME|# #;(> iter 80))
      (define-values (ς↑s ς↓s) (set-partition-to-lists -ς↑? front))

      (begin
        (when (debug-iter?)
          (printf "* ~a: ~a~n" iter (set-count front)))

        (when (debug-trace?)

          (begin ; interactive
            (define ςs-list
              (append ς↑s ς↓s))
            (define ς->i
              (for/hash : (HashTable -ς Integer) ([(ς i) (in-indexed ςs-list)])
                (values ς i))))
          
          (printf " * evs:~n")
          (for ([ς ς↑s])
            (printf "  -[~a]. ~a~n" (hash-ref ς->i ς) (show-ς ς)))
          (printf " * rts:~n")
          (for ([ς ς↓s])
            (printf "  -[~a]. ~a~n" (hash-ref ς->i ς) (show-ς ς)))

          #;(begin ; interactive
              (printf "~nchoose [0-~a|ok|done]: " (sub1 (hash-count ς->i)))
              (match (read)
                [(? exact-integer? i) (set! front (set (list-ref ςs-list i)))]
                ['done (error "DONE")]
                [_ (void)]))
          (printf "~n"))
        
        (set! iter (+ 1 iter)))

      (define next
        (match-let ([(-Σ σ mσₖ mM) Σ])

          (define vsn : Ctx (list σ mσₖ mM))

          (: ς-seen? : -ς → Boolean)
          (define (ς-seen? ς)
            (cond
              [(hash-ref seen ς #f) =>
               (λ ([ctx₀ : Ctx])
                 (match-define (list σ₀ mσₖ₀ mM₀) ctx₀)
                 (define αₖ
                   (match ς
                     [(-ς↑ αₖ _ _) αₖ]
                     [(-ς↓ αₖ _ _) αₖ]))
                 (define αₖs {set αₖ})
                 (define (κ->αₖs [κ : -κ])
                   {set (⟦k⟧->αₖ (-κ-cont κ))})
                 (and (map-equal?/spanning-root mσₖ₀ mσₖ αₖs κ->αₖs)
                      (map-equal?/spanning-root mM₀  mM  αₖs ΓA->αₖs)
                      (let ([⟪α⟫s (ς->⟪α⟫s ς mσₖ₀)])
                        (σ-equal?/spanning-root σ₀ σ ⟪α⟫s))))]
              [else #f]))

          (define next-from-ς↑s
            (let ([ς↑s* ; filter out seen states
                     (for*/list : (Listof -ς↑) ([ς ς↑s] #:unless (ς-seen? ς))
                       (hash-set! seen ς vsn)
                       (assert ς -ς↑?))])
              (↝↑! ς↑s* Σ)))
          (define next-from-ς↓s
            (let ([ς↓s* ; filter out seen states
                     (for*/list : (Listof -ς↓) ([ς ς↓s] #:unless (ς-seen? ς))
                       (hash-set! seen ς vsn)
                       (assert ς -ς↓?))])
              (↝↓! ς↓s* Σ)))
          (∪ next-from-ς↑s next-from-ς↓s)))
      (loop! next)))
  

  (match-let ([(-Σ σ σₖ M) Σ])
    (when (debug-iter?)
      (printf "|σ| = ~a, |σₖ| = ~a, |M| = ~a~n"
              (hash-count (-σ-m σ))
              (hash-count σₖ)
              (hash-count M)))
    (values (M@ M αₖ₀) Σ)))

(: ς->⟪α⟫s : -ς (HashTable -αₖ (℘ -κ)) → (℘ ⟪α⟫))
;; Compute the root set for value addresses of this state
(define (ς->⟪α⟫s ς σₖ)
  (match ς
    [(-ς↑ αₖ _ _)
     (define αs₀
       (match αₖ
         [(-ℬ _ _ ρ #;_) (->⟪α⟫s ρ)]
         [(-ℳ _ _ _ C ⟪α⟫) (set-add (->⟪α⟫s C) ⟪α⟫)]
         [(-ℱ _ _ _ C ⟪α⟫) (set-add (->⟪α⟫s C) ⟪α⟫)]
         [(-ℋ𝒱) {seteq ⟪α⟫ₕᵥ}]))
     (∪ αs₀ (αₖ->⟪α⟫s αₖ σₖ))]
    [(-ς↓ αₖ _ A) ; if it's a "return" state, don't care about block content (e.g. `ρ`)
     (define αs₀ (if (-W? A) (->⟪α⟫s A) ∅eq))
     (∪ αs₀ (αₖ->⟪α⟫s αₖ σₖ))]))

(: ↝↑! : (Listof -ς↑) -Σ → (℘ -ς))
;; Quick-step on "push" state
(define (↝↑! ςs Σ)
  (for/union : (℘ -ς) ([ς ςs])
    (match-define (-ς↑ αₖ Γ ⟪ℋ⟫) ς)
    (define ⟦k⟧ (rt αₖ))
    (match αₖ
      [(-ℬ _ ⟦e⟧ ρ #;_) (⟦e⟧ ρ $∅ Γ ⟪ℋ⟫ Σ ⟦k⟧)]
      [(-ℳ x l³ ℒ C ⟪α⟫)
       (define W-C (-W¹ C #f))
       (define 𝐱 (-x x))
       (for/union : (℘ -ς) ([V (in-set (σ@ (-Σ-σ Σ) ⟪α⟫))])
         (mon l³ $∅ ℒ W-C (-W¹ V 𝐱) Γ ⟪ℋ⟫ Σ ⟦k⟧))]
      [(-ℱ x l  ℒ C ⟪α⟫)
       (define W-C (-W¹ C #f))
       (define 𝐱 (-x x))
       (for/union : (℘ -ς) ([V (in-set (σ@ (-Σ-σ Σ) ⟪α⟫))])
          (flat-chk l $∅ ℒ W-C (-W¹ V 𝐱) Γ ⟪ℋ⟫ Σ ⟦k⟧))]
      [(-ℋ𝒱) (havoc ⟪ℋ⟫ Σ)]
      [_ (error '↝↑ "~a" αₖ)])))

(: ↝↓! : (Listof -ς↓) -Σ → (℘ -ς))
;; Quick-step on "pop" state
(define (↝↓! ςs Σ)
  (match-define (-Σ σ σₖ M) Σ)
  
  (for/union : (℘ -ς) ([ς ςs])
    (match-define (-ς↓ αₖ Γₑₑ A) ς)
    (define fml : (Option -formals)
      (match αₖ
        [(-ℬ xs _ _) xs]
        [(-ℳ x _ _ _ _) (list x)]
        [(-ℱ x _ _ _ _) (list x)]
        [(? -ℋ𝒱?) #f]))

    (for/union : (℘ -ς) ([κ (in-set (σₖ@ σₖ αₖ))])
      (match-define (-κ ⟦k⟧ Γₑᵣ ⟪ℋ⟫ₑᵣ tₓs) κ)
      (define looped? (equal? αₖ (⟦k⟧->αₖ ⟦k⟧)))
      (match A
        [(-W Vs sₐ)
         (define sₐ*
           (and sₐ
                (match* (αₖ tₓs)
                  [((? -ℳ?) (list t)) t]
                  [((-ℬ (list x) _ _) (list t)) ; inline some
                   #:when (and (not looped?)
                               (match? sₐ (-t.@ (? -o? o) (list (-x (== x))))))
                   (match-define (-t.@ o _) sₐ)
                   (?t@ o t)]
                  [((-ℬ (? list? xs) _ _) ts)
                   #:when (and (-x? sₐ)
                               (memq (-x-₀ sₐ) xs)
                               (not (and looped? (>= (length xs) 3))))
                   (for/or : -?t ([z xs] [t ts] #:when (eq? z (-x-₀ sₐ)))
                     t)]
                  [(_ _) (apply ?t@ αₖ tₓs)])))
         (define Γₑᵣ*
           (cond
             [looped? Γₑᵣ]
             [fml (inv-callee->caller σ ∅eq fml tₓs Γₑᵣ Γₑₑ)]
             [else Γₑᵣ]))
         (if Γₑᵣ* (⟦k⟧ (-W Vs sₐ*) $∅ Γₑᵣ* ⟪ℋ⟫ₑᵣ Σ) ∅)]
        [(? -blm? blm)
         (match-define (-blm l+ lo _ _ _) blm)
         (cond [(symbol? l+) ∅]
               [else (⟦k⟧ blm $∅ Γₑᵣ ⟪ℋ⟫ₑᵣ Σ)])]))))
