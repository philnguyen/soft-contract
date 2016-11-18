#lang typed/racket/base

(provide run-file havoc-file run-e)

(require "../utils/main.rkt"
         "../ast/main.rkt"
         "../parse/main.rkt"
         "../runtime/main.rkt"
         "../proof-relation/main.rkt"
         "compile/utils.rkt"
         "compile/kontinuation.rkt"
         "compile/main.rkt"
         "init.rkt"
         racket/set
         racket/match
         (only-in racket/list split-at))

(: run-file : Path-String → (Values (℘ -ΓA) -Σ))
(define (run-file p)
  (with-initialized-static-info
    (define m (file->module p))
    (define-values (σ₁ _) (𝑰 (list m)))
    (run (↓ₘ m) σ₁)))

(: havoc-file : Path-String → (Values (℘ -ΓA) -Σ))
(define (havoc-file p)
  (with-initialized-static-info
    (define m (file->module p))
    (define-values (σ₁ e₁) (𝑰 (list m)))
    (run (↓ₚ (list m) e₁) σ₁)))

(: run-e : -e → (Values (℘ -ΓA) -Σ))
(define (run-e e)
  (with-initialized-static-info
    (define-values (σ₀ _) (𝑰 '()))
    (run (↓ₑ 'top e) σ₀)))

(define-type Ctx (List (HashTable -⟪α⟫ (℘ -V)) (HashTable -αₖ (℘ -κ))))

(: run : -⟦e⟧! -σ → (Values (℘ -ΓA) -Σ))
(define (run ⟦e⟧! σ)
  (define seen : (HashTable -ς Ctx) (make-hash))
  (define αₖ₀ : -αₖ (-ℬ '() ⟦e⟧! ⊥ρ))
  (define Σ (-Σ σ (⊥σₖ αₖ₀) (⊥M)))

  (define iter : Natural 0)

  (let loop! ([front : (℘ -ς) {set (-ς↑ αₖ₀ ⊤Γ ⟪ℋ⟫∅)}])
    (unless (or (set-empty? front) #|FIXME|# #;(> iter 80))

      (begin
        (define num-front (set-count front))
        (define-values (ς↑s ς↓s) (set-partition-to-lists -ς↑? front))
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
              (append (set->list ς↑s) (set->list ς↓s)))
            (define ς->i
              (for/hash : (HashTable -ς Integer) ([(ς i) (in-indexed ςs-list)])
                (values ς i))))
          
          (printf " *~n")
          (for ([ς ς↑s])
            (printf "  -[~a]. ~a~n" (hash-ref ς->i ς) (show-ς ς)))
          (printf " *~n")
          (for ([ς ς↓s])
            (printf "  -[~a]. ~a~n" (hash-ref ς->i ς) (show-ς ς)))

          (begin ; interactive
              (printf "~nchoose [0-~a|ok|done]: " (sub1 (hash-count ς->i)))
              (match (read)
                [(? exact-integer? i) (set! front (set (list-ref ςs-list i)))]
                ['done (error "DONE")]
                [_ (void)]))
          )
        
        (printf "~n")
        (set! iter (+ 1 iter)))
      
      (define next
        (let ([ς↦αs : (HashTable -ς (℘ -⟪α⟫)) (make-hash)]
              [ς↦αₖs : (HashTable -ς (℘ -αₖ)) (make-hash)]
              [ς↦vsn : (HashTable -ς Ctx) (make-hash)]
              [αs-all : (℘ -⟪α⟫) ∅eq])
          ;; Compute each state's active addresses in the frontier
          (match-define (-Σ (and σ (-σ mσ _ _)) mσₖ _) Σ)
          (for ([ς front])
            (define αₖs (ς->αₖs ς mσₖ))
            (define αs (span* mσ (ς->⟪α⟫s ς mσₖ) V->⟪α⟫s #:eq? #t))
            (define vsn (list (m↓ mσ αs) (m↓ mσₖ αₖs)))
            (set! αs-all (∪ αs-all αs))
            (hash-set! ς↦αₖs ς αₖs)
            (hash-set! ς↦αs ς αs)
            (hash-set! ς↦vsn ς vsn))
          (soft-gc! σ (span* mσ αs-all V->⟪α⟫s #:eq? #t))
          (define next-from-ς↑s
            (let ([ς↑s* ; filter out seen states
                     (for*/list : (Listof -ς↑) ([ς ς↑s]
                                                [vsn (in-value (hash-ref ς↦vsn ς))]
                                                #:unless (equal? vsn (hash-ref seen ς #f)))
                     (hash-set! seen ς vsn)
                     (assert ς -ς↑?))])
              (↝↑! ς↑s* Σ)))
          (define next-from-ς↓s
            (let ([ς↓s* ; filter out seen states
                     (for*/list : (Listof -ς↓) ([ς ς↓s]
                                                [vsn (in-value (hash-ref ς↦vsn ς))]
                                                #:unless (equal? vsn (hash-ref seen ς #f)))
                       (hash-set! seen ς vsn)
                       (assert ς -ς↓?))])
              (↝↓! ς↓s* Σ)))
          (∪ next-from-ς↑s next-from-ς↓s)))
      (loop! next)))

  (match-let ([(-Σ σ σₖ M) Σ])
    (values (M@ M αₖ₀) Σ)))

(: ς->⟪α⟫s : -ς (HashTable -αₖ (℘ -κ)) → (℘ -⟪α⟫))
;; Compute the root set for value addresses of this state
(define (ς->⟪α⟫s ς σₖ)
  (match ς
    [(-ς↑ αₖ _ _)
     (define αs₀
       (match αₖ
         [(-ℬ _ _ ρ) (->⟪α⟫s ρ)]
         [(-ℳ _ _ _ (-W¹ C _) (-W¹ V _)) (∪ (->⟪α⟫s C) (->⟪α⟫s V))]
         [(-ℱ _ _ _ (-W¹ C _) (-W¹ V _)) (∪ (->⟪α⟫s C) (->⟪α⟫s V))]))
     (∪ αs₀ (αₖ->⟪α⟫s αₖ σₖ))]
    [(-ς↓ αₖ _ A) ; if it's a "return" state, don't care about block content (e.g. `ρ`)
     (define αs₀ (if (-W? A) (->⟪α⟫s A) ∅eq))
     (∪ αs₀ (αₖ->⟪α⟫s αₖ σₖ))]))

(: ς->αₖs : -ς (HashTable -αₖ (℘ -κ)) → (℘ -αₖ))
;; Compute all relevant stack addresses
(define (ς->αₖs ς σₖ)
  (define αₖ
    (match ς
      [(-ς↑ αₖ _ _) αₖ]
      [(-ς↓ αₖ _ _) αₖ]))
  (span-σₖ σₖ αₖ))

(: ↝↑! : (Listof -ς↑) -Σ → (℘ -ς))
;; Quick-step on "push" state
(define (↝↑! ςs Σ)
  (for/union : (℘ -ς) ([ς ςs])
    (match-define (-ς↑ αₖ Γ ⟪ℋ⟫) ς)
    (define ⟦k⟧ (rt αₖ))
    (match αₖ
      [(-ℬ _ ⟦e⟧! ρ)
       (⟦e⟧! ρ $∅ Γ ⟪ℋ⟫ Σ ⟦k⟧)]
      [(-ℳ _ l³ ℓ W-C W-V)
       (mon l³ $∅ ℓ W-C W-V Γ ⟪ℋ⟫ Σ ⟦k⟧)]
      [(-ℱ _ l ℓ W-C W-V)
       (flat-chk l $∅ ℓ W-C W-V Γ ⟪ℋ⟫ Σ ⟦k⟧)]
      [_
       (error '↝↑ "~a" αₖ)])))

(: ↝↓! : (Listof -ς↓) -Σ → (℘ -ς))
;; Quick-step on "pop" state
(define (↝↓! ςs Σ)
  
  ;; To mitigate duplicate returns
  (define-type Key (List -κ (U -blm (Pairof (Listof -V) Boolean))))
  (define returned : (HashTable Key #t) (make-hash))
  (match-define (-Σ σ σₖ M) Σ)

  ;(define hits : Natural 0)
  ;(define total : Natural 0)
  
  (define ans (for/union : (℘ -ς) ([ς ςs])
    (match-define (-ς↓ αₖ Γₑₑ A) ς)
    (for/union : (℘ -ς) ([κ (σₖ@ σₖ αₖ)])
      (match-define (-κ ⟦k⟧ Γₑᵣ ⟪ℋ⟫ₑᵣ sₕ sₓs) κ)
      (define fargs (apply -?@ sₕ sₓs))
      ;(set! total (+ 1 total))
      (match A
        [(-W Vs sₐ)
         (define key : Key (list κ (cons Vs (and sₐ #t))))
         (cond
           [(hash-has-key? returned key)
            ;(set! hits (+ 1 hits))
            ∅]
           [else
            (define γ (-γ αₖ #f sₕ sₓs))
            (define Γₑᵣ* (-Γ-plus-γ Γₑᵣ γ))
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
                               (values {seteq x} (if sₓ (hash-set m∅ (-x x) sₓ) m∅))])])
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
                (apply Γ+ Γₑᵣ* φ-ans (set->list φs-path))))
            (cond
              [(or #;(no-obvious-conflict? Γₑᵣ γ Γₑₑ)
                   (plausible-pc? M Γₑᵣ**))
               (hash-set! returned key #t)
               (define sₐ*
                 (and sₐ
                      (match fargs ; HACK
                        [(-@ 'fc (list x) _)
                         (match Vs
                           [(list (-b #f)) -ff]
                           [(list (-b #t) _) (-?@ 'values -tt x)])]
                        [_ fargs])))
               #;(define σ (-Σ-σ Σ))
               #;(define Vs* : (Listof -V)
                   (for/list ([V Vs] [s (split-values sₐ* (length Vs))])
                     (V+ σ V (predicates-of Γₑₑ s))))
               (⟦k⟧ (-W Vs sₐ*) $∅ Γₑᵣ* ⟪ℋ⟫ₑᵣ Σ)]
              [else ∅])])]
        [(? -blm? blm) ; TODO: faster if had next `αₖ` here 
         (match-define (-blm l+ lo _ _) blm)
         (define key (list κ blm))
         (cond
           [(hash-has-key? returned key)
            ;(set! hits (+ 1 hits))
            ∅]
           [else
            (case l+
              [(havoc † Λ) ∅]
              [else
               (define γ (-γ αₖ (cons l+ lo) sₕ sₓs))
               (define Γₑᵣ* (-Γ-plus-γ Γₑᵣ γ))
               (cond
                 [(or (no-obvious-conflict? Γₑᵣ γ Γₑₑ)
                      (plausible-pc? M Γₑᵣ*))
                  (hash-set! returned key #t)
                  (⟦k⟧ blm $∅ Γₑᵣ* ⟪ℋ⟫ₑᵣ Σ)]
                 [else ∅])])])]))))
  ;(printf "  -- hits: ~a/~a~n" hits total)
  ans)

(: no-obvious-conflict? : -Γ -γ -Γ → Boolean)
;; Heuristic check that there's no need for heavyweight SMT call
;; to filter out spurious return/blame
(define (no-obvious-conflict? Γₑᵣ γ Γₑₑ)

  (: talks-about? : -Γ -e → Boolean)
  (define (talks-about? Γ e)
    (match-define (-Γ φs _ γs) Γ)
    (or (for/or : Boolean ([φ φs])
          (e-talks-about? φ e))
        (for/or : Boolean ([γ γs])
          (match-define (-γ _ _ sₕ sₓs) γ)
          (or (and sₕ (e-talks-about? sₕ e))
              (for/or : Boolean ([sₓ sₓs] #:when sₓ)
                (e-talks-about? sₓ e))))))

  (: e-talks-about? : -e -e → Boolean)
  (define (e-talks-about? e₁ e₂)
    (let loop ([e : -e e₁])
      (or (equal? e e₂)
          (match e
            [(-@ eₕ es _) (or (loop eₕ) (ormap loop es))]
            [_ #f]))))

  (match-define (-γ αₖ _ sₕ sₓs) γ)

  (match αₖ
    [(-ℬ (? list? xs) _ _)
     (not (or (for/or : Boolean ([x xs] [sₓ sₓs])
                (and sₓ
                     (Γₑᵣ . talks-about? . sₓ)
                     (Γₑₑ . talks-about? . (-x x))))
              (for/or : Boolean ([x (if sₕ (fv sₕ) ∅eq)])
                (and (Γₑᵣ . talks-about? . (-x x))
                     (Γₑₑ . talks-about? . (-x x))))))]
    [(-ℳ x _ _ _ (-W¹ _ sₓ))
     (not (and sₓ
               (Γₑᵣ . talks-about? . sₓ)
               (Γₑₑ . talks-about? . (-x x))))]
    [(-ℱ x _ _ _ (-W¹ _ sₓ))
     (not (and sₓ
               (Γₑᵣ . talks-about? . sₓ)
               (Γₑₑ . talks-about? . (-x x))))]
    [_ #f]))
