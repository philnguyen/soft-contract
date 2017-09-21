#lang typed/racket/base

(provide reduction@)

(require racket/set
         racket/match
         racket/list
         typed/racket/unit
         set-extras
         "../utils/main.rkt"
         "../ast/signatures.rkt"
         "../runtime/signatures.rkt"
         "../proof-relation/signatures.rkt"
         "../primitives/signatures.rkt"
         "../signatures.rkt"
         "signatures.rkt"

         "compile.rkt"
         "app.rkt"
         "mon.rkt"
         "kont.rkt"
         "havoc.rkt"
         "memoize.rkt"
         )

(define-unit pre-reduction@
  (import static-info^ kont^ havoc^ mon^ compile^ local-prover^ widening^ verifier^
          for-gc^ env^ sto^ ast-pretty-print^ pretty-print^ pc^ instr^ summ^)
  (export reduction^)

  (define-type Ctx (List -σ -σₖ))

  (define (run [⟦e⟧ : -⟦e⟧]) : (Values (℘ -ΓA) -Σ)
    (define seen : (HashTable -ς Ctx) (make-hash))
    (define αₖ₀ : -αₖ (-ℬ ⊤$ ⟪ℋ⟫∅ '() ⟦e⟧ ⊥ρ ⊤Γ))
    (define Σ (-Σ ⊥σ (hash-set ⊥σₖ αₖ₀ ∅) ⊥M ⊥𝒜 ⊥Ξ))
    (define root₀ ; all addresses to top-level definitions are conservatively active
      (for/fold ([root₀ : (℘ ⟪α⟫) ∅eq]) ([𝒾 (top-levels)])
        (set-add (set-add root₀ (-α->⟪α⟫ 𝒾)) (-α->⟪α⟫ (-α.wrp 𝒾)))))

    (define iter : Natural 0)
    (define ?max-steps (max-steps))
    (define iter-maxed? : (Natural → Boolean)
      (if ?max-steps (λ ([i : Natural]) (> i ?max-steps)) (λ _ #f)))

    (let loop! ([front : (℘ -ς) {set (-ς↑ αₖ₀)}])
      (unless (or (set-empty? front) (iter-maxed? iter))
        (define-values (ς↑s ς↓s) (set-partition-to-lists -ς↑? front))

        (begin
          (when (debug-iter?)
            (printf "* ~a: ~a~n" iter (set-count front)))

          #;(match-let ([(-Σ σ σₖ _ _ _) Σ])
            (printf "  |σ| = ~a, max-rng(σ) = ~a, |σₖ| = ~a, max-rng(σₖ) = ~a~n"
                    (hash-count σ) (count-max σ) (hash-count σₖ) (count-max σₖ)))

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
          (match-let ([(-Σ σ mσₖ _ _ _) Σ])

            (define vsn : Ctx (list σ mσₖ))

            (: ς-seen? : -ς → Boolean)
            (define (ς-seen? ς)
              (cond
                [(hash-ref seen ς #f) =>
                 (λ ([ctx₀ : Ctx])
                   (match-define (list σ₀ mσₖ₀) ctx₀)
                   (define (κ->αₖs [κ : -κ])
                     {set (⟦k⟧->αₖ (-κ-rest κ))})
                   (and (map-equal?/spanning-root mσₖ₀ mσₖ {set (-ς-block ς)} κ->αₖs)
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

    (match-let ([(-Σ σ σₖ _ _ _) Σ])
      (when (debug-iter?)
        (printf "|σ| = ~a, |σₖ| = ~a~n" (hash-count σ) (hash-count σₖ)))
      (when (and ?max-steps (> iter ?max-steps))
        (printf "Execution capped at ~a steps~n" ?max-steps))
      #;(let ()
        (define ℬ-stats : (HashTable (List -formals -⟦e⟧ -ρ) (℘ -$)) (make-hash))
        (define ℋ-stats : (HashTable -⟪ℋ⟫ (℘ -$)) (make-hash))
        (for ([αₖ (in-hash-keys σₖ)])
          (match αₖ
            [(-ℬ $ _ xs e ρ _)
             (hash-update! ℬ-stats (list xs e ρ)
                           (λ ([$s : (℘ -$)])
                             (set-add $s $))
                           mk-∅)]
            [(-ℋ𝒱 $ ⟪ℋ⟫)
             (hash-update! ℋ-stats ⟪ℋ⟫
                           (λ ([$s : (℘ -$)])
                             (set-add $s $))
                           mk-∅)]
            [_ (void)]))
        (printf "ℬ-stats: (~a --> ~a) ~n" (hash-count ℬ-stats) (length (filter -ℬ? (hash-keys σₖ))))

        (define (show-$-stats [vs : (℘ -$)])
          (define m : (HashTable -loc (℘ -?t)) (make-hash))
          (for ([$ : -$ (in-set vs)])
            (for ([(l t) (in-hash $)])
              (hash-update! m l (λ ([ts : (℘ -?t)]) (set-add ts t)) mk-∅)))
          (for ([l (in-hash-keys m)])
            (for ([$ (in-set vs)] #:unless (hash-has-key? $ l))
              (hash-update! m l (λ ([ts : (℘ -?t)]) (set-add ts #f)))))
          (for ([(l ts) (in-hash m)] #:when (> (set-count ts) 1))
            (printf "  + ~a -> ~a~n" (show-loc l) (set-count ts))
            (for ([t (in-set ts)])
              (printf "    * ~a~n" (show-t t)))))
        
        (for ([(k vs) (in-hash ℬ-stats)] #:when (> (set-count vs) 10))
          (match-define (list xs e ρ) k)
          (printf "- ~a ~a --> ~a~n" (show-formals xs) (show-ρ ρ) (set-count vs))
          (show-$-stats vs))
        (printf "ℋ-stats: (~a --> ~a) ~n" (hash-count ℋ-stats) (length (filter -ℋ𝒱? (hash-keys σₖ))))
        (for ([(k vs) (in-hash ℋ-stats)] #:when (> (set-count vs) 10))
          (printf "- ~a --> ~a~n" (show-⟪ℋ⟫ k) (set-count vs))
          (show-$-stats vs))
        
        #;(printf "Value store:~n")
        #;(for ([(α Vs) (in-hash σ)]
              ;#:when (> (set-count Vs) 1)
              ;#:unless (equal? α ⟪α⟫ₕᵥ)
              )
          (printf "- ~a ↦ ~a~n" (show-⟪α⟫ α) (set-map Vs show-V)))
        (printf "Stack store:~n")
        (for ([(αₖ ks) (in-hash σₖ)]
              #:when (> (set-count ks) 15)
              #:unless (-ℋ𝒱? αₖ)
              )
          (printf "- ~a ↦ ~a~n" (show-αₖ αₖ) (set-count ks))
          #;(let ([comp : (Mutable-HashTable (Pairof Any Integer) (℘ Any)) (make-hash)])
            (define-set explodes : Any)
            (for ([k (in-set ks)])
              (match-define (-κ.rt ⟦k⟧ _ _ _ _) k)
              (match-let* ([(list _ ⟦k⟧) (find-memo-key ⟦k⟧ 'invalidate-$∷)]
                           [(list _ ⟦k⟧) (find-memo-key ⟦k⟧ 'restore-$∷)]
                           [(list _ ⟦k⟧) (find-memo-key ⟦k⟧ 'restore-ctx∷)]
                           [(list _ _ _ _ ⟦k⟧) (find-memo-key ⟦k⟧ 'ap∷)]
                           [(list Ws es _ ℓ₀ _) (find-memo-key ⟦k⟧ 'ap∷)]
                           [(list tag (list elems ...)) (find-memo-key ⟦k⟧)])
                (explodes-add! (list Ws es ℓ₀))
                (for ([e (in-list elems)] [i (in-naturals)])
                  (hash-update! comp (cons tag i)
                                (λ ([s : (℘ Any)]) (set-add s e))
                                mk-∅))))
            (for ([(k vs) (in-hash comp)])
              (printf "    - ~a : ~a~n" k (set-count vs)))
            (begin
              (printf "explodes:~n")
              (for ([e (in-set explodes)])
                (match-define (list Ws es ℓ₀) e)
                (printf "- ~a [ ] ~a at ~a~n"
                        (map show-W¹ (reverse (cast Ws (Listof -W¹))))
                        (map show-⟦e⟧ (cast es (Listof -⟦e⟧)))
                        (show-ℓ (cast ℓ₀ ℓ)))))
            )
          ))
      (values (M@ Σ αₖ₀) Σ)))

  ;; Compute the root set for value addresses of this state
  (define (ς->⟪α⟫s [ς : -ς] [σₖ : -σₖ]) : (℘ ⟪α⟫)
    (match ς
      [(-ς↑ αₖ)
       (define αs₀
         (match αₖ
           [(-ℬ _ _ _ _ ρ _) (->⟪α⟫s ρ)]
           [(-ℳ _ _ _ C V _) (∪ (->⟪α⟫s C) (->⟪α⟫s V))]
           [(-ℱ _ _ _ _ C V _) (∪ (->⟪α⟫s C) (->⟪α⟫s V))]
           [(-ℋ𝒱 _ _) {seteq ⟪α⟫ₕᵥ}]))
       (∪ αs₀ (αₖ->⟪α⟫s αₖ σₖ))]
      [(-ς↓ αₖ _ _ A) ; if it's a "return" state, don't care about block content (e.g. `ρ`)
       (define αs₀ (if (-W? A) (->⟪α⟫s A) ∅eq))
       (∪ αs₀ (αₖ->⟪α⟫s αₖ σₖ))]))

  ;; Quick-step on "push" state
  (define (↝↑! [ςs : (Listof -ς↑)] [Σ : -Σ]) : (℘ -ς)
    (for/union : (℘ -ς) ([ς ςs])
               (match-define (-ς↑ αₖ ) ς)
               (define ⟦k⟧ (rt αₖ))
               (match αₖ
                 [(-ℬ $ ⟪ℋ⟫ fmls ⟦e⟧ ρ Γ)
                  #;(begin
                    (printf "executing ~a:~n" (show-⟦e⟧ ⟦e⟧))
                    (printf "env:~n")
                    (for ([(x α) (in-hash ρ)])
                      (printf "  ~a ↦ ~a~n" x (show-⟪α⟫ α)))
                    (printf "cache:~n")
                    (for ([(l W) (in-hash $)])
                      (printf "  ~a ↦ ~a~n" (show-loc l) (show-W¹ W)))
                    (printf "~n"))
                  (⟦e⟧ ρ $ Γ ⟪ℋ⟫ Σ ⟦k⟧)]
                 [(-ℳ $ ⟪ℋ⟫ ctx W-C W-V Γ)
                  (mon ctx W-C W-V $ Γ ⟪ℋ⟫ Σ ⟦k⟧)]
                 [(-ℱ $ ⟪ℋ⟫ l ℓ W-C W-V Γ)
                  (flat-chk l ℓ W-C W-V $ Γ ⟪ℋ⟫ Σ ⟦k⟧)]
                 [(-ℋ𝒱 $ ⟪ℋ⟫) (havoc $ ⟪ℋ⟫ Σ ⟦k⟧)]
                 [_ (error '↝↑ "~a" αₖ)])))

  ;; Quick-step on "pop" state
  (define (↝↓! [ςs : (Listof -ς↓)] [Σ : -Σ]) : (℘ -ς)
    (define σₖ (-Σ-σₖ Σ))
    (define σ (-Σ-σ Σ))

    (: continue : -κ -A -$ -Γ -αₖ → (℘ -ς))
    (define (continue κ A $ Γₐ αₖₑₑ)
      (define ⟪ℋ⟫ (-αₖ-ctx αₖₑₑ))
      (match κ
        [(-κ.rt ⟦k⟧ dom Γ t looped?)
         (match A
           [(-W Vs tₐ)
            (define name-from-callee?
              (match* (tₐ αₖₑₑ)
                [((? integer? ℓ) (-ℬ _ _ _ ⟦e⟧ _ _)) (loc-from-expr? ℓ ⟦e⟧)]
                [(_ _) #f]))
            (define-values (tₐ* Γ*)
              (cond [looped? (values t Γ)]
                    [name-from-callee? (values t Γ)]
                    [else (values tₐ (copy-Γ dom Γ Γₐ))]))
            (⟦k⟧ (-W Vs tₐ*) $ Γ* ⟪ℋ⟫ Σ)]
           [_ (⟦k⟧ A $ Γ ⟪ℋ⟫ Σ)])]
        [(-κ ⟦k⟧)
         (⟦k⟧ A $ Γₐ ⟪ℋ⟫ Σ)]))

    (for/union : (℘ -ς) ([ς ςs])
      (match-define (-ς↓ αₖₑₑ $ₑₑ Γₑₑ A) ς)
      (for/union : (℘ -ς) ([κ (in-set (σₖ@ σₖ αₖₑₑ))])
        (continue κ A $ₑₑ Γₑₑ αₖₑₑ))))
  )

(define-compound-unit/infer reduction@
  (import ast-pretty-print^ static-info^ meta-functions^
          prims^ proof-system^ local-prover^ widening^ verifier^
          for-gc^ val^ env^ sto^ pc^ instr^ pretty-print^ prim-runtime^ summ^)
  (export reduction^ app^ mon^ kont^ compile^ havoc^)
  (link memoize@ kont@ compile@ havoc@ mon@ app@ pre-reduction@))
