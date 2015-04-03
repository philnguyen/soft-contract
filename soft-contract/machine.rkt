#lang typed/racket/base
(require
 racket/match racket/set racket/list racket/bool racket/function
 "utils.rkt" "lang.rkt" "runtime.rkt" "show.rkt" "provability.rkt" "delta.rkt")

(provide (all-defined-out)) ; TODO

(define-data .κ
  (struct .if/κ [t : .E] [e : .E])
  (struct .let/κ [xs : (Listof .expr)] [vs : (Listof .V)]
                 [env : .ρ] [body : .expr]) ;FIXME generalize to `let-values`
  (struct .@/κ [e* : (Listof .E)] [v* : (Listof .V)] [ctx : Mon-Party])
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
  (match? ς (.ς (? .blm?) _ _) (.ς (? .V?) _ (list))))

(: inj : .expr → .ς)
(define (inj e)
  (.ς (.↓ e ρ∅) σ∅ empty))

(define-syntax-rule (match/nd v [p e ...] ...) (match/nd: (.Ans → .ς) v [p e ...] ...))

(: print-ς : .ς → Void)
(define (print-ς ς)
  (define it (show-ς ς))
  (printf "E:~n ~a~n" (second (first it)))
  (printf "σ:~n")
  (for ([x (rest (second it))])
    (printf " ~a~n" x))
  (printf "k:~n")
  (for ([x (rest (third it))])
    (printf " ~a~n" x)))

(: and/ς : (Listof .E) .σ .κ* → .ς)
(define (and/ς E* σ k)
  (match E*
    ['() (.ς TT σ k)]
    [(list E) (.ς E σ k)]
    [(cons E Er)
     (.ς E σ (foldr (λ ([Ei : .E] [k : .κ*])
                      (cons (.if/κ Ei FF) k))
                    k Er))]))

(: or/ς : (Listof .E) .σ .κ* → .ς)
(define (or/ς E* σ k)
  (match E*
    ['() (.ς FF σ k)]
    [(list E) (.ς E σ k)]
    [(cons E Er)
     (.ς E σ (foldr (λ ([Ei : .E] [k : .κ*])
                      (cons (.if/κ TT Ei) k))
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

(: show-k : .σ .κ* → (Listof Any))
(define (show-k σ k) (for/list ([κ k]) (show-κ σ κ)))

(: show-κ : .σ .κ → Any)
(define (show-κ σ κ)
  (define E (curry show-E σ))
  (match κ
    [(.if/κ t e) `(if ∘ ,(E t) ,(E e))]
    [(.let/κ xs vs ρ e) `(let …)]
    [(.@/κ e* v* _) `(@ ,@(reverse (map E v*)) ∘ ,@(map E e*))]
    [(.▹/κ (cons #f (? .E? e)) _) `(∘ ▹ ,(E e))]
    [(.▹/κ (cons (? .E? C) #f) _) `(,(E C) ▹ ∘)]
    [(.indy/κ Cs xs xs↓ d _ _) `(indy ,(map E Cs) ,(map E xs) ,(map E xs↓)
                                      ,(match d [#f '_] [(? .E? d) (E d)]))]
    [(.μc/κ x) `(μ/c ,x ∘)]
    [(.λc/κ cs Cs d ρ _) `(λ/c (,@(reverse (map E Cs)) ,@(map (curry show-e σ) cs)) ,(show-e σ d))]
    [(.structc/κ t c _ c↓) `(struct/c ,t (,@(reverse (map E c↓)) ,(map (curry show-e σ) c)))]
    [(.rt/κ _ f x) `(rt ,(E (→V f)) ,@(map E x))]
    [(.blr/κ _ _ V) `(blr ,(E V))]
    [(.recchk/κ c v) `(μ/▹ ,(E (→V c)) ,(E v))]))

(: show-ς : .ς → (List (Listof Any) (Listof Any) (Listof Any)))
(define show-ς
  (match-lambda
    [(.ς E σ k) `((E: ,(if (.E? E) (show-E σ E) (show-κ σ (car E))))
                  (σ: ,@(show-σ σ))
                  (k: ,@(show-k σ k)))]))
