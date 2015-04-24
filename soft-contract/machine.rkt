#lang typed/racket/base
(require
 racket/match racket/set racket/list racket/bool racket/function
 "utils.rkt" "lang.rkt" "runtime.rkt" "show.rkt" "provability.rkt" "delta.rkt")

(provide (all-defined-out)) ; TODO

(define-data .κ
  (struct .if/κ [t : .E] [e : .E])
  (struct .let-values/κ
    [pending-arity : Integer]
    [bnds : (Listof (Pairof Integer .expr))]
    [vals : (Listof .V)]
    [env : .ρ]
    [body : .expr]
    [ctx : Mon-Party])
  #;(struct .let/κ [xs : (Listof .expr)] [vs : (Listof .V)]
                 [env : .ρ] [body : .expr]) ;FIXME generalize to `let-values`
  (struct .@/κ [e* : (Listof .E)] [v* : (Listof .V)] [ctx : Mon-Party])
  (struct .begin/κ [es : (Listof .expr)] [ρ : .ρ])
  (struct .begin0v/κ [es : (Listof .expr)] [ρ : .ρ])
  (struct .begin0e/κ [V : .V] [es : (Listof .expr)] [ρ : .ρ])
  (struct .▹/κ [ce : (U (Pairof #f .E) (Pairof .V #f))] [l³ : Mon-Info])
  (struct .indy/κ
    [c : (Listof .V)] [x : (Listof .V)] [x↓ : (Listof .V)]
    [d : (U #f .↓)] [v? : (U #f Integer)] [l³ : Mon-Info])
  ;; contract stuff
  (struct .μc/κ [x : Symbol])
  (struct .λc/κ [c : (Listof .expr)] [c↓ : (Listof .V)] [d : .expr] [ρ : .ρ] [v? : Boolean])
  (struct .structc/κ [t : .id] [c : (Listof .expr)] [ρ : .ρ] [c↓ : (Listof .V)])
  ;; magics for termination. `ce` does not use these
  (struct .rt/κ [σ : .σ] [f : .λ↓] [x : (Listof .V)])
  (struct .blr/κ [F : .F] [σ : .σ] [v : .V])
  (struct .recchk/κ [c : .μ/C] [v : .V]) ; where all labels are fully resolved
  ;p experiment
  (struct .μ/κ [F : .μ/V] [xs : (Listof .V)] [σ : .σ]))
(define-type .κ* (Listof .κ))

;; ctx in e's position for pending states
(struct .ς ([e : (U (Pairof .rt/κ .F) .E)] [s : .σ] [k : .κ*]) #:transparent)
(define-type .ς+ (Setof .ς))
(define-type .ς* (U .ς .ς+))

(: final? : .ς → Boolean)
(define (final? ς)
  (match? ς (.ς (? .blm?) _ _) (.ς (? .Vs?) _ (list))))

(: inj : .expr → .ς)
(define (inj e)
  (.ς (.↓ e ρ∅) σ∅ empty))

(define-syntax-rule (match/nd v [p e ...] ...) (match/nd: (.Ans → .ς) v [p e ...] ...))

(: and/ς : (Listof .E) .σ .κ* → .ς)
(define (and/ς E* σ k)
  (match E*
    ['() (.ς -VsTT σ k)]
    [(list E) (.ς E σ k)]
    [(cons E Er)
     (.ς E σ (foldr (λ ([Ei : .E] [k : .κ*])
                      (cons (.if/κ Ei -VsFF) k))
                    k Er))]))

(: or/ς : (Listof .E) .σ .κ* → .ς)
(define (or/ς E* σ k)
  (match E*
    ['() (.ς -VsFF σ k)]
    [(list E) (.ς E σ k)]
    [(cons E Er)
     (.ς E σ (foldr (λ ([Ei : .E] [k : .κ*])
                      (cons (.if/κ -VsTT Ei) k))
                    k Er))]))

(: ▹/κ1 : .V Mon-Info .κ* → .κ*)
(define (▹/κ1 C l³ k)
  (match C
    [(.// (.λ↓ (.λ 1 (.b #t)) _) _) k]
    [(.// (? .Λ/C?) _) (cons (.▹/κ (cons C #f) l³) k)]
    [_ (cons (.▹/κ (cons C #f) l³)
             (let trim : .κ* ([k : .κ* k])
               (match k
                 [(cons (and κ (.▹/κ (cons (? .V? D) #f) _)) kr)
                  (match (C⇒C C D)
                    ['✓ (trim kr)]
                    [_ (cons κ (trim kr))])]
                 [_ k])))]))

(: show-k : .σ .κ* → (Listof Sexp))
(define (show-k σ k) (for/list ([κ k]) (show-κ σ κ)))

(: show-κ : .σ .κ → Sexp)
(define (show-κ σ κ)
  (define E (curry show-E σ))
  (define V (curry show-V σ))
  (match κ
    [(.if/κ t e) `(if ∘ ,(E t) ,(E e))]
    [(? .let-values/κ?) '(let-values …)]
    [(.@/κ e* v* _) `(@ ,@(reverse (map V v*)) ∘ ,@(map E e*))]
    [(.▹/κ (cons #f (? .E? e)) _) `(∘ ▹ ,(E e))]
    [(.▹/κ (cons (? .V? C) #f) _) `(,(V C) ▹ ∘)]
    [(.indy/κ Cs xs xs↓ d _ _) `(indy ,(map V Cs) ,(map V xs) ,(map V xs↓)
                                      ,(match d [#f '_] [(? .E? d) (E d)]))]
    [(.μc/κ x) `(μ/c ,x ∘)]
    [(.λc/κ cs Cs d ρ _) `(λ/c (,@(reverse (map V Cs)) ,@(map (curry show-e σ) cs)) ,(show-e σ d))]
    [(.structc/κ t c _ c↓) `(struct/c ,(.id-name t) (,@(reverse (map V c↓)) ,(map (curry show-e σ) c)))]
    [(.rt/κ _ f x) `(rt ,(V (→V f)) ,@(map V x))]
    [(.blr/κ _ _ v) `(blr ,(V v))]
    [(.recchk/κ c v) `(μ/▹ ,(V (→V c)) ,(V v))]))

(: show-ek : .σ .κ* Sexp → Sexp)
(define (show-ek σ k acc)

  (for/fold ([acc : Sexp acc]) ([κ (in-list k)])
    (match κ
      [(.if/κ E₁ E₂) `(if ,acc ,(show-E σ E₁) ,(show-E σ E₂))]
      [(.let-values/κ _n bnds Vs _ρ e _ctx)
       `(let-values (,@(reverse (show-Vs σ Vs))
                     (□ ← ,acc)
                     ,@(for/list : (Listof Sexp) ([bnd (in-list bnds)])
                         (show-e σ (cdr bnd))))
          ,(show-e σ e))]
      [(.@/κ Es Vs _ctx)
       `(,@(reverse (show-Vs σ Vs)) ,acc ,@(map (curry show-E σ) Es))]
      [(.begin/κ es _)
       `(begin ,acc ,@(map (curry show-e σ) es))]
      [(.begin0v/κ es _)
       `(begin0 ,acc ,@(map (curry show-e σ) es))]
      [(.begin0e/κ V es _)
       `(begin0 ,(show-V σ V) ,acc ,@(map (curry show-e σ) es))]
      [(.▹/κ ce _)
       (cond [(.E? (cdr ce)) `(mon ,acc ,(show-E σ (cdr ce)))]
             [(.V? (car ce)) `(mon ,(show-V σ (car ce)) ,acc)]
             [else (error 'Internal "show-ek: unexpected case")])]
      [(.indy/κ Cs Xs Xs↓ D _v? _)
       (cond
         [D
          `(mon ,(show-E σ D)
                (,@(reverse (show-Vs σ Xs↓))
                 ,acc
                 ,@(for/list : (Listof Sexp) ([Cᵢ Cs] [Vᵢ Xs])
                     `(mon ,(show-V σ Cᵢ) ,(show-V σ Vᵢ)))))]
         [else
          `(mon ,acc
                (,@(reverse (show-Vs σ Xs↓))
                 ,@(for/list : (Listof Sexp) ([Cᵢ Cs] [Vᵢ Xs])
                     `(mon ,(show-V σ Cᵢ) ,(show-V σ Vᵢ)))))])]
      [(.μc/κ x) `(μ/c ,x ,acc)]
      [(.λc/κ cs Cs d _ρ _)
       `(→i (,@(reverse (show-Vs σ Cs)) ,acc ,@(map (curry show-e σ) cs))
            ,(show-e σ d))]
      [(.structc/κ t cs _ Cs)
       `(,(.id-name t) ,@(reverse (show-Vs σ Cs)) ,acc ,@(map (curry show-e σ) cs))]
      [(.rt/κ _ _ _) `(rt ,acc)]
      [(.blr/κ _ _ _) `(blr ,acc)]
      [(.recchk/κ _ _) `(recchk ,acc)]
      [(.μ/κ _ _ _) `(μ/κ ,acc)])))

(: show-ς : .ς → (List (Listof Sexp) (Listof Sexp) (Listof Sexp)))
(define show-ς
  (match-lambda
    [(and ς (.ς E σ k))
     `((E: ,(if (.E? E) (show-E σ E) (show-κ σ (car E))))
       (σ: ,@(show-σ σ))
       (k: ,@(show-k σ k)))]))

(: print-ς : .ς → Void)
(define (print-ς ς)
  (match-define (.ς E σ k) ς)
  (parameterize ([abstract-V? #f])
    (cond [(.E? E)
           (printf "---- E: ~a~n     σ: ~a~n~n"
                   (show-ek σ k `(⦃,(show-E σ E)⦄))
                   (show-σ σ))]
          [else
           (printf "---- K: ~a~n     σ: ~a~n~n"
                   (show-ek σ k `(⟦,(show-κ σ (car E))⟧))
                   (show-σ σ))])))
