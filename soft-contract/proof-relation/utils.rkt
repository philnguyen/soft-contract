#lang typed/racket/base

(provide (all-defined-out))

(require
 racket/match racket/set
 "../utils/non-det.rkt" "../utils/set.rkt" "../utils/untyped-macros.rkt"
 "../ast/definition.rkt" "../ast/meta-functions.rkt"
 "../runtime/addr.rkt" "../runtime/val.rkt" "../runtime/summ.rkt" "../runtime/store.rkt" "../runtime/simp.rkt" "../runtime/path-inv.rkt"
 "local.rkt")

(: invert-e : -M -σ -id (Listof -e) → (Setof -Res))
;; Given proposition `(p? v)`, generate an overapproximation of expressions
;; that could have evaluated to it
(define (invert-e M σ f args)
  (define ans
    (match f
    [(-id o 'Λ)
     {set (-Res (apply -?@ o args) ∅)}]
    [_
     (define α (-α.def f))
     (match/nd: (-V → -Res) (σ@ σ α)
       [(or (-Clo (? list? xs) e _ _) (-Clo* (? list? xs) e _))
        ;; Convert invariant about parameters into one about arguments
        (define convert
          (e/map
           (for/hash : (HashTable -e -e) ([x (assert xs)] [arg args])
             (values (-x x) arg))))
        
        (match/nd: (-Res → -Res) (hash-ref M (assert e))
          [(-Res e-xs ψ-xs)
           (define e-args (and e-xs (convert e-xs)))
           (define ψ-args (map/set convert ψ-xs))
           (-Res e-args ψ-args)])]
       [_ -Res⊤])]))
  ;(printf "insert-e: ~a ~a ↦ ~a~n" f (map show-e args) (map show-Res (set->list ans)))
  ans)

(: invert-Γ : -M -σ -Γ → (Setof -Γ))
;; Given propositions `Γ`, generate an overapproximation of environments
;; that could have derived it
(define (invert-Γ M σ Γ)
  (match-define (-Γ bnds facts) Γ)

  ; split environment into propositions that can be further unrolled and the rest
  (define-values (ψs-unrollable ψs₀)
    (set-partition (match-λ? (-@ (? -ref?) _ _)) facts))

  (: go : (Setof -Γ) (Listof -e) → (Setof -Γ))
  ; Join each base environment in `Γs` with each possible inversion of `φs`
  (define (go Γs φs)
    (match φs
      ['() Γs]
      [(cons φ φs*)
       (match-define (-@ (-ref id _ _) xs _) φ)
       (for*/fold ([acc : (Setof -Γ) ∅])
                  ([kase : -Res (invert-e M σ id xs)]
                   [Γ : -Γ (go Γs φs*)])
         (match-define (-Res ψ_i ψs_i) kase)
         (define Γ₁ (if ψ_i (Γ⊓e Γ ψ_i) Γ))
         (define Γ₂ (and Γ₁ (Γ⊓ Γ₁ ψs_i)))
         (if Γ₂ (set-add acc Γ₂) acc))]))

  (go (set (-Γ bnds ψs₀)) (set->list ψs-unrollable)))

(: unfold ([-M -σ -e] [(-id (Listof -e) → Boolean)] . ->* . (Option (Setof -Res))))
;; Unfold the first appropriate expression according to `unfold-this-one?`.
;; Return #f if couldn't find one to unfold.
(define (unfold M σ e₀ [unfold-this-one? (λ (id args) #t)])

  (: go : -e → (Option (Setof -Res)))
  (define (go e)
    (define ans
      (match e
      [(-@ f xs l)
       (match (go* (cons f xs))
         [#f
          (match f
            [(-ref id _ _)
             (and
              (unfold-this-one? id xs)
              (for/set: : (Setof -Res) ([res (invert-e M σ id xs)])
                (match-define (-Res (? -e? e*) ψs) res)
                (define ψs* ; strengthen with induction hypotheses
                  (for/fold ([ψs* : -es ψs]) ([args (find-calls e* id)])
                    (define hyp (e/list xs args e₀))
                    (set-add ψs* hyp)))
                (-Res e* ψs*)))]
            [_ #f])]
         [(? set? reses)
          (for/set: : (Setof -Res) ([res reses])
            (match-define (cons (cons f* xs*) ψs) res)
            (-Res (apply -?@ f* xs*) ψs))])]
      [_ #|TODO just this for now|# #f]))
    ;(printf "go: ~a ↦ ~a~n" e (and ans (map show-Res (set->list ans))))
    ans)

  (: go* : (Listof -e) → (Option (Setof (Pairof (Listof -e) -es))))
  (define (go* es)
    (define ans
    (match es
      ['() #f]
      [(cons e es*)
       (match (go e)
         [#f
          (match (go* es*)
            [#f #f]
            [(? set? reses)
             (for/set: : (Setof (Pairof (Listof -e) -es)) ([res reses])
               (match-define (cons es** ψs) res)
               (cons (cons e es**) ψs))])]
         [(? set? reses)
          (for/set: : (Setof (Pairof (Listof -e) -es)) ([res reses])
            (match-define (-Res (? -e? #|FIXME|# e*) ψs) res)
            (cons (cons e* es*) ψs))])]))
    ;(printf "go*: ~a ↦ ~a~n" es ans)
    ans)

  (go e₀))

(: ⇓₁ : -M -σ -Γ -e → (Values -e -Γ))
;; Unfold/evaluate expression only if there's only 1 branch 
(define (⇓₁ M σ Γ e)

  (: go : -Γ -e → (Values -e -Γ))
  (define (go Γ e)
    (match e
      [(-@ f xs _)
       (define-values (fxs* Γ*) (go* Γ (cons f xs)))
       (match-define (cons f* xs*) fxs*)
       (match f*
         [(-ref id _ _)
          (define reses*
            (for*/set: : (Setof (Pairof -e -Γ))
                       ([res (invert-e M σ id xs*)]
                        [ψs (in-value (-Res-facts res))]
                        [Γ* (in-value (Γ⊓ Γ ψs))] #:when Γ*)
              (cons (assert (-Res-e res)) Γ*)))
          (cond
            [(= 1 (set-count reses*))
             (match-define (cons e* Γ*) (set-first reses*))
             (go Γ* (assert e*))]
            [else (values (assert (apply -?@ f* xs*)) Γ)])]
         [_ (values (assert (apply -?@ f* xs*)) Γ)])]
      [_ (values e Γ)]))

  (: go* : -Γ (Listof -e) → (Values (Listof -e) -Γ))
  (define (go* Γ es)
    (define-values (es↓ Γ*)
      (for/fold ([es↓ : (Listof -e) '()] [Γ : -Γ Γ]) ([e es])
        (define-values (e* Γ*) (go Γ e))
        (values (cons e* es↓) Γ*)))
    (values (reverse es↓) Γ*))
  
  (go Γ e))
