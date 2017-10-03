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

  (: print-large-sets ([-Σ] [#:val-min Index #:kont-min Index #:ctx-min Index] . ->* . Void))
  (define (print-large-sets Σ #:val-min [val-min 4] #:kont-min [kont-min 4] #:ctx-min [ctx-min 4])
    (define σ (-Σ-σ Σ))
    (define σₖ (-Σ-σₖ Σ))
    (define B-stats : (HashTable (List -formals -⟦e⟧ -ρ) (℘ -$)) (make-hash))
    (define ℋ-stats : (HashTable -l (℘ -$)) (make-hash))
    (for ([αₖ (in-hash-keys σₖ)])
      (match αₖ
        [(-B $ _ xs e ρ _)
         (hash-update! B-stats (list xs e ρ)
                       (λ ([$s : (℘ -$)]) (set-add $s $))
                       mk-∅)]
        [(-HV $ t)
         (hash-update! ℋ-stats t
                       (λ ([$s : (℘ -$)]) (set-add $s $))
                       mk-∅)]
        [_ (void)]))
    (printf "B-stats: (~a --> ~a) ~n" (hash-count B-stats) (length (filter -B? (hash-keys σₖ))))
    
    (for ([(k vs) (in-hash B-stats)] #:when (> (set-count vs) 15))
      (match-define (list xs e ρ) k)
      (printf "- ~a ~a --> ~a~n" (show-formals xs) (show-ρ ρ) (set-count vs))
      (print-$-grid #;show-$-stats vs))
    (for ([(k vs) (in-hash ℋ-stats)] #:when (> (set-count vs) 15))
      (match-define l k)
      (printf "- ~a --> ~a~n" l (set-count vs))
      (print-$-grid #;show-$-stats vs))

    (begin
      (printf "Value store:~n")
      (for ([(α Vs) (in-hash σ)]
            #:when (>= (set-count Vs) val-min)
            #:unless (match? (⟪α⟫->-α α) (-α.hv '†))
            )
        (printf "- ~a ↦ ~a~n" (show-⟪α⟫ α) (set-map Vs show-V)))
      #;(printf "Addresses:~n")
      #;(for ([α (in-hash-keys σ)])
        (printf "~a ≡ ~a~n" (show-⟪α⟫ α) (⟪α⟫->-α α)))
      )

    (let ([ctxs : (Mutable-HashTable Symbol (℘ -H)) (make-hasheq)])
      (for ([α (in-hash-keys σ)])
        (match (⟪α⟫->-α α)
          [(-α.x x H _) (map-add! ctxs x H #:eq? #t)]
          [_ (void)]))
      (for ([(x Hs) (in-hash ctxs)] #:when (>= (set-count Hs) ctx-min))
        (printf "~a ↦ ~a~n" x (set-count Hs))
        (for ([H : -H (in-set Hs)])
          (match (-H->-ℋ H)
            ['() (printf "  - ()~n")]
            [(cons e es)
             (printf "  - ~a~n" (show-edge e))
             (for ([e (in-list es)])
               (printf "    ~a~n" (show-edge e)))]))))
    

    (begin
      (printf "Stack store:~n")
      (for ([(αₖ ks) (in-hash σₖ)]
            #:when (>= (set-count ks) kont-min)
            #:unless (-HV? αₖ)
            )
        (printf "- ~a ↦ ~a~n" (show-αₖ αₖ) (set-count ks))
        #;(let ([comp : (Mutable-HashTable (Pairof Any Integer) (℘ Any)) (make-hash)])
          (for ([k (in-set ks)])
            (match-define (-κ.rt ⟦k⟧ _ _ _ _) k)
            (match-for* ([(list tag elem*) (find-memo-key (last elems))])
              (match elem*
                [(list elems ...)
                 (for ([e (in-list elems)] [i (in-naturals)])
                   (hash-update! comp (cons tag i)
                                 (λ ([s : (℘ Any)]) (set-add s e))
                                 mk-∅))]
                [_
                 (hash-update! comp (cons tag -1)
                               (λ ([s : (℘ Any)]) (set-add s elem*))
                               mk-∅)])))
          (for ([(k vs) (in-hash comp)])
            (printf "    - ~a : ~a~n" k (set-count vs)))
          )
        ))
    ))
