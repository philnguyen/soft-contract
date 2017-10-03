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
         "debugging.rkt"
         )

(define-unit pre-reduction@
  (import static-info^ kont^ havoc^ mon^ compile^ local-prover^ widening^ verifier^
          val^ for-gc^ env^ sto^ ast-pretty-print^ pretty-print^ pc^ instr^ summ^
          debugging^)
  (export reduction^)

  (define-type Ctx (List -σ -σₖ))

  (define (run [⟦e⟧ : -⟦e⟧]) : (Values (℘ -A) -Σ)
    (define seen : (HashTable -ς Ctx) (make-hash))
    (define αₖ₀ : -αₖ (-B ⊤$ H∅ '() ⟦e⟧ ⊥ρ ⊤Γ))
    (define Σ (-Σ ⊥σ (hash-set ⊥σₖ αₖ₀ ∅) ⊥𝒜 ⊥Ξ))
    (define root₀ ; all addresses to top-level definitions are conservatively active
      (for/fold ([root₀ : (℘ ⟪α⟫) ∅eq]) ([𝒾 (top-levels)])
        (set-add (set-add root₀ (-α->⟪α⟫ 𝒾)) (-α->⟪α⟫ (-α.wrp 𝒾)))))

    (define iter : Natural 0)
    (define ?max-steps (max-steps))
    (define iter-maxed? : (Natural → Boolean)
      (if ?max-steps (λ ([i : Natural]) (> i ?max-steps)) (λ _ #f)))
    (define-set errs : -blm)

    (let loop! ([front : (℘ -ς) {set (-ς↑ αₖ₀)}])
      #;(when (iter-maxed? iter)
        (print-stat front))
      (unless (or (set-empty? front) (iter-maxed? iter))
        (define-values (ς↑s ς↓s ς!s) (partition-states front))

        (begin
          (when (debug-iter?)
            (printf "* ~a: ~a~n" iter (set-count front))
            #;(printf " -- ~a are rt, ~a are ev~n" (length ς↓s) (length ς↑s)))

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
        (for ([ς (in-list ς!s)])
          (match-define (-blm l+ lo C V ℓ) (-ς!-blm ς))
          (errs-add! (-blm l+ lo C V (strip-ℓ ℓ))))
        (loop! next)))

    (match-let ([(-Σ σ σₖ _ _) Σ])
      (when (debug-iter?)
        (printf "|σ| = ~a, |σₖ| = ~a~n" (hash-count σ) (hash-count σₖ)))
      (when (and ?max-steps (> iter ?max-steps))
        (printf "Execution capped at ~a steps~n" ?max-steps))
      #;(print-large-sets Σ #:val-min 1 #:kont-min 1)
      (values errs Σ)))

  ;; Compute the root set for value addresses of this state
  (define (ς->⟪α⟫s [ς : -ς] [σₖ : -σₖ]) : (℘ ⟪α⟫)
    (match ς
      [(-ς↑ αₖ)
       (define αs₀
         (match αₖ
           [(-B _ _ _ _ ρ _) (->⟪α⟫s ρ)]
           [(-M _ _ _ C V _) (∪ (->⟪α⟫s C) (->⟪α⟫s V))]
           [(-F _ _ _ _ C V _) (∪ (->⟪α⟫s C) (->⟪α⟫s V))]
           [(-HV $ tag) {seteq (-α->⟪α⟫ (-α.hv tag))}]))
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
                 [(-B $ H fmls ⟦e⟧ ρ Γ)
                  #;(begin
                    (printf "executing ~a:~n" (show-⟦e⟧ ⟦e⟧))
                    (printf "env:~n")
                    (for ([(x α) (in-hash ρ)])
                      (printf "  ~a ↦ ~a~n" x (show-⟪α⟫ α)))
                    (printf "cache:~n")
                    (for ([(l t) (in-hash $)])
                      (printf "  ~a ↦ ~a~n" (show-loc l) (show-t t)))
                    (printf "pc: ~a~n" (show-Γ Γ))
                    (printf "~n"))
                  #;(cond
                    [(hash-ref ρ 'x₁ #f)
                     =>
                     (λ ([α : ⟪α⟫])
                       (match-define (-α.x _ H) (⟪α⟫->-α α))
                       (printf "ctx for x₁ at ~a: (~a) ~n" (show-⟪α⟫ α) (show-H H))
                       (for ([e (in-list (-H->-ℋ H))])
                         (printf "- ~a~n" (show-edge e))))])
                  (⟦e⟧ ρ $ Γ H Σ ⟦k⟧)]
                 [(-M $ H ctx W-C W-V Γ)
                  (mon ctx W-C W-V $ Γ H Σ ⟦k⟧)]
                 [(-F $ H l ℓ W-C W-V Γ)
                  (flat-chk l ℓ W-C W-V $ Γ H Σ ⟦k⟧)]
                 [(-HV $ tag) (havoc tag $ Σ ⟦k⟧)]
                 [_ (error '↝↑ "~a" αₖ)])))

  ;; Quick-step on "pop" state
  (define (↝↓! [ςs : (Listof -ς↓)] [Σ : -Σ]) : (℘ -ς)
    (define σₖ (-Σ-σₖ Σ))
    (define σ (-Σ-σ Σ))

    (: continue : -κ -A -$ -Γ -αₖ → (℘ -ς))
    (define (continue κ A $ Γₐ αₖₑₑ)
      (define H (-αₖ-ctx αₖₑₑ))
      (match κ
        [(-κ.rt ⟦k⟧ dom Γ t looped? bnds)
         (match A
           [(-W Vs tₐ)
            (define name-from-callee?
              (match* (tₐ αₖₑₑ)
                [((? integer? ℓ) (-B _ _ _ ⟦e⟧ _ _)) (loc-from-expr? ℓ ⟦e⟧)]
                [(_ _) #f]))
            (define tₐ*
              (match tₐ
                ;; FIXME generalize hack
                [(-b (or 0 #t #f)) tₐ]
                [(-t.x x)
                 #:when (and (hash-has-key? bnds x)
                             (match? αₖₑₑ (-B _ _ (or (list _) (list _ _)) _ _ _)))
                 (hash-ref bnds x)]
                [(-t.@ '- (list (-t.x x) (? -b? b)))
                 #:when (and (hash-has-key? bnds x)
                             (match? αₖₑₑ (-B _ _ (or (list _) (list _ _)) _ _ _)))
                 (-t.@ '- (list (hash-ref bnds x) b))]
                [_
                 (cond [looped? t]
                       [name-from-callee? t]
                       [else tₐ])]))
            (define Γ* : -Γ
              (let ([Γ₀ (if looped? Γ (copy-Γ (∪ dom (fvₜ tₐ)) Γ Γₐ))])
                (define δΓ
                  (for/union : (℘ -?t) ([V (in-list Vs)] [t (in-list (split-values tₐ* (length Vs)))])
                             (for/set: : (℘ -?t) ([p (in-set (predicates-of-V V))])
                       (?t@ p t))))
                (apply Γ+ Γ₀ (filter values (set->list δΓ)))))
            (⟦k⟧ (-W Vs tₐ*) $ Γ* H Σ)]
           [_ (⟦k⟧ A $ Γ H Σ)])]
        [(-κ ⟦k⟧)
         (⟦k⟧ A $ Γₐ H Σ)]))

    (for/union : (℘ -ς) ([ς ςs])
      (match-define (-ς↓ αₖₑₑ $ₑₑ Γₑₑ A) ς)
      (for/union : (℘ -ς) ([κ (in-set (σₖ@ σₖ αₖₑₑ))])
        (continue κ A $ₑₑ Γₑₑ αₖₑₑ))))

  (: -αₖ-ctx : -αₖ → -H)
  (define (-αₖ-ctx α)
    (cond [(-B? α) (-B-ctx α)]
          [(-M? α) (-M-ctx α)]
          [(-F? α) (-F-ctx α)]
          [else H∅]))

  (: partition-states : (℘ -ς) → (Values (Listof -ς↑) (Listof -ς↓) (Listof -ς!)))
  (define (partition-states ςs)
    (for/fold ([ς↑s : (Listof -ς↑) '()]
               [ς↓s : (Listof -ς↓) '()]
               [ς!s : (Listof -ς!) '()])
              ([ς (in-set ςs)])
      (cond [(-ς↑? ς) (values (cons ς ς↑s) ς↓s ς!s)]
            [(-ς↓? ς) (values ς↑s (cons ς ς↓s) ς!s)]
            [else     (values ς↑s ς↓s (cons (assert ς -ς!?) ς!s))])))
  )

(define-compound-unit/infer reduction@
  (import ast-pretty-print^ static-info^ meta-functions^
          prims^ proof-system^ local-prover^ widening^ verifier^
          for-gc^ val^ env^ sto^ pc^ instr^ pretty-print^ prim-runtime^ summ^)
  (export reduction^ app^ mon^ kont^ compile^ havoc^)
  (link debugging@ memoize@ kont@ compile@ havoc@ mon@ app@ pre-reduction@))
