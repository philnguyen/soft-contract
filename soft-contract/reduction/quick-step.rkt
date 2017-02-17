#lang typed/racket/base

(provide run)

(require racket/set
         racket/match
         racket/list
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

(define-type Ctx (List (HashTable ⟪α⟫ (℘ -V))
                       (HashTable -αₖ (℘ -κ))
                       (HashTable -αₖ (℘ -ΓA))))

(: run : -⟦e⟧ → (Values (℘ -ΓA) -Σ))
(define (run ⟦e⟧)
  (define seen : (HashTable -ς Ctx) (make-hash))
  (define αₖ₀ : -αₖ (-ℬ '() ⟦e⟧ ⊥ρ))
  (define Σ (-Σ ⊥σ (hash-set ⊥σₖ αₖ₀ ∅) ⊥M))
  (define root₀ ; all addresses to top-level definitions are conservatively active
    (for/fold ([root₀ : (℘ ⟪α⟫) ∅eq]) ([𝒾 (top-levels)])
      (set-add (set-add root₀ (-α->⟪α⟫ 𝒾)) (-α->⟪α⟫ (-α.wrp 𝒾)))))

  (define iter : Natural 0)

  (let loop! ([front : (℘ -ς) {set (-ς↑ αₖ₀ ⊤Γ ⟪ℋ⟫∅)}])
    (unless (or (set-empty? front) #|FIXME|# #;(> iter 80))
      (define-values (ς↑s ς↓s) (set-partition-to-lists -ς↑? front))

      (begin
        (define num-front (set-count front))
        (printf "* ~a: ~a" iter num-front )
        ;(printf " (~a + ~a)" (length ς↑s) (length ς↓s))
        #;(printf "; cfgs: ~a, max(σₖ): ~a, max(M): ~a"
                  (hash-count seen)
                  (apply max 0 ((inst map Natural (℘ -κ)) set-count (hash-values (-Σ-σₖ Σ))))
                  (apply max 0 ((inst map Natural (℘ -ΓA)) set-count (hash-values (-Σ-M Σ)))))
        (printf "~n")

        #;(begin ; verbose

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
          )
        
        (printf "~n")
        (set! iter (+ 1 iter)))

      (define next
        (match-let ([(-Σ (and σ (-σ mσ _ _)) mσₖ mM) Σ])

          (define vsn : Ctx (list mσ mσₖ mM))

          (: ς-seen? : -ς → Boolean)
          (define (ς-seen? ς)
            (cond
              [(hash-ref seen ς #f) =>
               (λ ([ctx₀ : Ctx])
                 (match-define (list mσ₀ mσₖ₀ mM₀) ctx₀)
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
                        (map-equal?/spanning-root mσ₀ mσ ⟪α⟫s V->⟪α⟫s))))]
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
    (values (M@ M αₖ₀) Σ)))

(: ς->⟪α⟫s : -ς (HashTable -αₖ (℘ -κ)) → (℘ ⟪α⟫))
;; Compute the root set for value addresses of this state
(define (ς->⟪α⟫s ς σₖ)
  (match ς
    [(-ς↑ αₖ _ _)
     (define αs₀
       (match αₖ
         [(-ℬ _ _ ρ) (->⟪α⟫s ρ)]
         [(-ℳ _ _ _ C ⟪α⟫) (set-add (->⟪α⟫s C) ⟪α⟫)]
         [(-ℱ _ _ _ C ⟪α⟫) (set-add (->⟪α⟫s C) ⟪α⟫)]
         [(-ℋ𝒱* _ Vs) (->⟪α⟫s Vs)]
         [(-ℋ𝒱  _ V ) (->⟪α⟫s V )]))
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
      [(-ℬ _ ⟦e⟧ ρ) (⟦e⟧ ρ $∅ Γ ⟪ℋ⟫ Σ ⟦k⟧)]
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
      [(-ℋ𝒱* ℒ Vs) (havoc* ℒ Vs Γ ⟪ℋ⟫ Σ ⟦k⟧)]
      [(-ℋ𝒱  ℒ V ) (havoc  ℒ V  Γ ⟪ℋ⟫ Σ ⟦k⟧)]
      [_ (error '↝↑ "~a" αₖ)])))

(: ↝↓! : (Listof -ς↓) -Σ → (℘ -ς))
;; Quick-step on "pop" state
(define (↝↓! ςs Σ)
  
  ;; To mitigate duplicate returns
  (define-type Key (List -κ -αₖ (U -blm (Pairof (Listof -V) Boolean))))
  (define returned : (HashTable Key #t) (make-hash))
  (match-define (-Σ σ σₖ M) Σ)

  ;(define hits : Natural 0)
  ;(define total : Natural 0)
  
  (with-debugging/off ((ans) (for/union : (℘ -ς) ([ς ςs])
    (match-define (-ς↓ αₖ Γₑₑ A) ς)
    (for/union : (℘ -ς) ([κ (σₖ@ σₖ αₖ)])
      (match-define (-κ ⟦k⟧ Γₑᵣ ⟪ℋ⟫ₑᵣ sₕ sₓs) κ)
      (define fargs (apply -?@ sₕ sₓs))
      ;(set! total (+ 1 total))
      (match A
        [(-W Vs sₐ)
         (define key : Key (list κ αₖ (cons Vs (and sₐ #t))))
         (cond
           [(hash-has-key? returned key)
            ;(set! hits (+ 1 hits))
            ∅]
           [else
            (define γ (-γ αₖ #f sₕ sₓs))
            (define Γₑᵣ**
              ; It's useful to check for feasibility of a strong path-condition
              ; before forgetting and keeping the path-condition address
              ; as an approximation
              ; TODO generalize
              (let-values ([(xs m)
                            (match αₖ
                              [(-ℬ xs _ _)
                               (define bounds (formals->names xs))
                               (define m
                                 (match xs
                                   [(? list? xs)
                                    (for/hash : Subst ([x xs] [sₓ sₓs] #:when sₓ)
                                      (values (-x x) sₓ))]
                                   [(-varargs xs x)
                                    (define-values (args-init args-rest) (split-at sₓs (length xs)))
                                    (define m-init
                                      (for/hash : Subst ([x xs] [arg args-init] #:when arg)
                                        (values (-x x) arg)))
                                    (define s-rst (-?list args-rest))
                                    (if s-rst (hash-set m-init (-x x) s-rst) m-init)]))
                               (values bounds m)]
                              [(-ℳ x _ _ _ _)
                               (define sₓ (car sₓs))
                               (values {seteq x} (if sₓ (hash-set m∅ (-x x) sₓ) m∅))]
                              [(-ℱ x _ _ _ _)
                               (define sₓ (car sₓs))
                               (values {seteq x} (if sₓ (hash-set m∅ (-x x) sₓ) m∅))]
                              [(-ℋ𝒱* _ _) (values ∅eq m∅)]
                              [(-ℋ𝒱  _ _) (values ∅eq m∅)])])
                (define φ-ans
                  (match Vs
                    [(list V)
                     (match V
                       [(? -v? v)
                        (-?@ 'equal? (apply -?@ sₕ sₓs) v)]
                       [(or (? -Clo?) (? -Ar?) (? -o?))
                        (-?@ 'procedure? (apply -?@ sₕ sₓs))]
                       [_ #f])]
                    [_ #f]))
                (define φs-path
                  (for/fold ([φs-path : (℘ -e) ∅]) ([φ (-Γ-facts Γₑₑ)])
                    (cond
                      [(⊆ (fv φ) xs) (set-add φs-path (e/map m φ))]
                      [else φs-path])))
                (apply Γ+ Γₑᵣ φ-ans (set->list φs-path))))
            (cond
              [#t #;(plausible-return? M Γₑᵣ** γ Γₑₑ)
               (hash-set! returned key #t)
               (define sₐ*
                 (and sₐ
                      (match fargs ; HACK
                        [(-@ 'fc (list x) _)
                         (match Vs
                           [(list (-b #f)) -ff]
                           [(list (-b #t) _) (-?@ 'values -tt x)])]
                        [_ fargs])))
               
               ;; Debugging
               #;(when (match? αₖ (-ℬ '(in₆) _ _))
                 (printf "~a~n - returns to ~a~n - value: ~a~n"
                         (show-αₖ αₖ) (show-κ κ) (show-A A))
                 (printf "results has:~n")
                 (for ([ΓA (M@ M αₖ)])
                   (printf "  - ~a~n" (show-ΓA ΓA)))
                 (printf "~n"))
               
               (⟦k⟧ (-W Vs sₐ*) $∅ (-Γ-plus-γ Γₑᵣ γ) ⟪ℋ⟫ₑᵣ Σ)]
              [else ∅])])]
        [(? -blm? blm) ; TODO: faster if had next `αₖ` here 
         (match-define (-blm l+ lo _ _) blm)
         (define key (list κ αₖ blm))
         (cond
           [(hash-has-key? returned key)
            ;(set! hits (+ 1 hits))
            ∅]
           [(symbol? l+) ; ignore blames on system
            ∅]
           [else
            (define γ (-γ αₖ (cons l+ lo) sₕ sₓs))
            (cond
              [#;#t (plausible-return? M Γₑᵣ γ Γₑₑ)
                  (hash-set! returned key #t)
                  (⟦k⟧ blm $∅ (-Γ-plus-γ Γₑᵣ γ) ⟪ℋ⟫ₑᵣ Σ)]
              [else ∅])])]))))
    (printf "  -- hits: ~a/~a~n" hits total)))


