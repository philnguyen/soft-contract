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
  (import static-info^ kont^ havoc^ mon^ local-prover^ widening^ verifier^
          for-gc^ env^ sto^ pretty-print^ pc^ instr^)
  (export reduction^)

  (define-type Ctx (List -σ -σₖ))

  (define (run [⟦e⟧ : -⟦e⟧]) : (Values (℘ -ΓA) -Σ)
    (define seen : (HashTable -ς Ctx) (make-hash))
    (define αₖ₀ : -αₖ (-ℬ ⊤$ ⟪ℋ⟫∅ '() ⟦e⟧ ⊥ρ ⊤Γ))
    (define Σ (-Σ ⊥σ (hash-set ⊥σₖ αₖ₀ ∅) ⊥M ⊥𝒜))
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

          #;(when (> (hash-count (-Σ-σₖ Σ)) 200)
            (define caches : (HashTable (Pairof -⟦e⟧ -ρ) (℘ -$)) (make-hash))
            (for ([αₖ (in-hash-keys (-Σ-σₖ Σ))])
              (when (-ℬ? αₖ)
                (define k (cons (-ℬ-exp αₖ) (-ℬ-env αₖ)))
                (hash-update! caches k (λ ([$s : (℘ -$)]) (set-add $s (-αₖ-cache αₖ))) mk-∅)))
            (for ([(eρ $s) (in-hash caches)] #:when (> (set-count $s) 10))
              (match-define (cons e ρ) eρ)
              (define bindings : (HashTable -loc (℘ (Option -W¹))) (make-hash))
              (define locs (for/union : (℘ -loc) ([$ (in-set $s)]) (dom $)))
              (for ([$ (in-set $s)])
                (for ([l (in-set locs)] #:unless (hash-has-key? $ l))
                  (hash-update! bindings l (λ ([Ws : (℘ (Option -W¹))]) (set-add Ws #f)) mk-∅))
                (for ([(l W) (in-hash $)])
                  (hash-update! bindings l (λ ([Ws : (℘ (Option -W¹))]) (set-add Ws W)) mk-∅)))
              (printf "~a bindings, ~a caches for ~a at ~a: ~n" (set-count locs) (set-count $s) (show-⟦e⟧ e) (show-ρ ρ))
              (for ([(l Ws) (in-hash bindings)] #:when (> (set-count Ws) 2))
                (printf "* ~a ↦ (~a)~n" (show-loc l) (set-count Ws))
                (for ([W (in-set Ws)])
                  (printf "  + ~a~n" (if W (show-W¹ W) '⊘))))
              (printf "~n"))
            (error "STOP"))

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
          (match-let ([(-Σ σ mσₖ _ _) Σ])

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

    (match-let ([(-Σ σ σₖ _ _) Σ])
      (when (debug-iter?)
        (printf "|σ| = ~a, |σₖ| = ~a~n" (hash-count σ) (hash-count σₖ)))
      (when (and ?max-steps (> iter ?max-steps))
        (printf "Execution capped at ~a steps~n" ?max-steps))
      #;(begin
        (printf "Value store:~n")
        (for ([(α Vs) (in-hash σ)]
              ;#:when (> (set-count Vs) 2)
              #:unless (equal? α ⟪α⟫ₕᵥ))
          (printf "- ~a ↦ ~a~n" (show-⟪α⟫ α) (set-map Vs show-V)))
        (printf "Stack store:~n")
        (for ([(αₖ ks) (in-hash σₖ)]
              #:when (> (set-count ks) 1)
              )
          (printf "- ~a ↦ ~a~n" (show-αₖ αₖ) (set-count ks))
          #|
          (define-set rests : -⟦k⟧)
          (define-set doms : (℘ Symbol))
          (define-set pcs : -Γ)
          (define-set looped?s : Boolean)
          (define-set anses : -?t)
          (for ([k (in-set ks)])
            (match-define (-κ.rt ⟦k⟧ dom Γ t looped?) k)
            (rests-add! ⟦k⟧)
            (doms-add! dom)
            (pcs-add! Γ)
            (anses-add! t)
            (looped?s-add! looped?))

          (printf "~a rests~n" (set-count rests))
          
          (printf "~a doms~n" (set-count doms))
          (for ([dom (in-set doms)])
            (printf "- ~a~n" (set->list dom)))
          (printf "~n")

          (printf "~a looppeds: ~a~n~n" (set-count looped?s) (set->list looped?s))

          (printf "~a anses:~n" (set-count anses))
          (for ([ans (in-set anses)])
            (printf "- ~a~n" (show-t ans)))
          (printf "~n")

          (printf "~a pcs:~n" (set-count pcs))
          (for ([pc (in-set pcs)])
            (printf "- ~a~n" (show-Γ pc)))
          |#
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

    (: continue : -κ -A -$ -Γ -⟪ℋ⟫ -Σ → (℘ -ς))
    (define (continue κ A $ Γₐ ⟪ℋ⟫ Σ)
      (match κ
        [(-κ.rt ⟦k⟧ dom Γ t looped?)
         (match A
           [(-W Vs tₐ)
            (define-values (tₐ* Γ*) (if looped? (values t Γ) (values tₐ (copy-Γ dom Γ Γₐ))))
            (⟦k⟧ (-W Vs tₐ*) $ Γ* ⟪ℋ⟫ Σ)]
           [_ (⟦k⟧ A $ Γ ⟪ℋ⟫ Σ)])]
        [(-κ ⟦k⟧)
         (⟦k⟧ A $ Γₐ ⟪ℋ⟫ Σ)]))
    
    (for/union : (℘ -ς) ([ς ςs])
      (match-define (-ς↓ αₖₑₑ $ₑₑ Γₑₑ A) ς)
      (for/union : (℘ -ς) ([κ (in-set (σₖ@ σₖ αₖₑₑ))])
        (continue κ A $ₑₑ Γₑₑ (-αₖ-ctx αₖₑₑ) Σ))))
  )

(define-compound-unit/infer reduction@
  (import ast-pretty-print^ static-info^ meta-functions^
          prims^ proof-system^ local-prover^ widening^ verifier^
          for-gc^ val^ env^ sto^ pc^ instr^ pretty-print^ prim-runtime^)
  (export reduction^ app^ mon^ kont^ compile^ havoc^)
  (link memoize@ kont@ compile@ havoc@ mon@ app@ pre-reduction@))
