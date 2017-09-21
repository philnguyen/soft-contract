#lang typed/racket/base

(provide debugging@)

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
         )

(define-unit debugging@
  (import static-info^ kont^ havoc^ mon^ compile^ local-prover^ widening^ verifier^
          for-gc^ env^ sto^ ast-pretty-print^ pretty-print^ pc^ instr^ summ^)
  (export debugging^)

  (: print-$-stat : (Sequenceof -$) → Void)
  (define (print-$-stat $s)
    (define m : (HashTable -loc (℘ -?t)) (make-hash))
    (for ([$ : -$ $s])
      (for ([(l t) (in-hash $)])
        (hash-update! m l (λ ([ts : (℘ -?t)]) (set-add ts t)) mk-∅)))
    (for ([l (in-hash-keys m)])
      (for ([$ $s] #:unless (hash-has-key? $ l))
        (hash-update! m l (λ ([ts : (℘ -?t)]) (set-add ts #f)))))
    (for ([(l ts) (in-hash m)] #:when (> (set-count ts) 1))
      (printf "  + ~a -> ~a~n" (show-loc l) (set-count ts))
      (for ([t (in-set ts)])
        (printf "    * ~a~n" (show-t t)))))

  (: print-$-grid : (Sequenceof -$) → Void)
  (define (print-$-grid $s)
    (define m : (HashTable -loc (℘ -?t)) (make-hash))
    (for ([$ : -$ $s])
      (for ([(l t) (in-hash $)])
        (hash-update! m l (λ ([ts : (℘ -?t)]) (set-add ts t)) mk-∅)))
    (for ([l (in-hash-keys m)])
      (for ([$ $s] #:unless (hash-has-key? $ l))
        (hash-update! m l (λ ([ts : (℘ -?t)]) (set-add ts #f)))))
    
    (define all-locs
      (for/list : (Listof -loc) ([(l ts) (in-hash m)] #:when (> (set-count ts) 1))
        l))
    (for ([l (in-list all-locs)])
      (printf "~a\t" (show-loc l)))
    (printf "~n")
    (for ([$ $s])
      (for ([l (in-list all-locs)])
        (printf "~a\t" (show-t (hash-ref $ l #f))))
      (printf "~n")))

  (: print-Σ-stat : -Σ → Void)
  (define (print-Σ-stat Σ)
    (define σ (-Σ-σ Σ))
    (define σₖ (-Σ-σₖ Σ))
    (printf "|σ| = ~a, max-rng(σ) = ~a, |σₖ| = ~a, max-rng(σₖ) = ~a~n"
            (hash-count σ) (count-max σ) (hash-count σₖ) (count-max σₖ)))

  (: print-large-sets ([-Σ] [#:val-min Index #:kont-min Index] . ->* . Void))
  (define (print-large-sets Σ #:val-min [val-min 4] #:kont-min [kont-min 4])
    (define σ (-Σ-σ Σ))
    (define σₖ (-Σ-σₖ Σ))
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
    
    (for ([(k vs) (in-hash ℬ-stats)] #:when (> (set-count vs) 4))
      (match-define (list xs e ρ) k)
      (printf "- ~a ~a --> ~a~n" (show-formals xs) (show-ρ ρ) (set-count vs))
      (print-$-grid #;show-$-stats vs))
    (printf "ℋ-stats: (~a --> ~a) ~n" (hash-count ℋ-stats) (length (filter -ℋ𝒱? (hash-keys σₖ))))
    (for ([(k vs) (in-hash ℋ-stats)] #:when (> (set-count vs) 4))
      (printf "- ~a --> ~a~n" (show-⟪ℋ⟫ k) (set-count vs))
      (print-$-grid #;show-$-stats vs))
    
    (printf "Value store:~n")
    (for ([(α Vs) (in-hash σ)]
          #:when (>= (set-count Vs) val-min)
          #:unless (equal? α ⟪α⟫ₕᵥ)
          )
      (printf "- ~a ↦ ~a~n" (show-⟪α⟫ α) (set-map Vs show-V)))
    (printf "Addresses:~n")
    (for ([α (in-hash-keys σ)])
      (printf "~a ≡ ~a~n" (show-⟪α⟫ α) (⟪α⟫->-α α)))
    
    (printf "Stack store:~n")
    (for ([(αₖ ks) (in-hash σₖ)]
          #:when (>= (set-count ks) kont-min)
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
      )))
