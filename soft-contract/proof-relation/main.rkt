#lang typed/racket/base

(provide proof-system@)

(require racket/match
         racket/set
         racket/bool
         typed/racket/unit
         syntax/parse/define
         set-extras
         "../utils/main.rkt"
         "../ast/main.rkt"
         "../runtime/main.rkt"
         "../signatures.rkt"
         "signatures.rkt")

(define-unit proof-system@
  (import (prefix loc: local-prover^) external-prover^ widening^)
  (export proof-system^)
  
  (define Γ⊢t loc:Γ⊢t)
  (define plausible-V-t? loc:plausible-V-t?)
  (define sat-one-of loc:sat-one-of)
  (define p∋Vs loc:p∋Vs)
  (define V-arity loc:V-arity)

  ;; Check if value satisfies (flat) contract
  (define (MΓ⊢V∈C [M : -M] [σ : -σ] [Γ : -Γ] [W_v : -W¹] [W_c : -W¹]) : -R
    (match-define (-W¹ V v) W_v)
    (match-define (-W¹ C c) W_c)
    (with-debugging/off
      ((ans)
       (first-R (loc:p∋Vs σ C (V+ σ V (predicates-of Γ v)))
                (match V
                  [(-● ps)
                   (define Γ*
                     (for/fold ([Γ : -Γ Γ]) ([p ps])
                       (Γ+ Γ (?t@ p v))))
                   (MΓ⊢t M Γ* (and (-h? c) (?t@ c v)))]
                  [_ (MΓ⊢t M Γ (and (-h? c) (?t@ c v)))])))
      (when (and (-Clo? V))
        (printf "~a ⊢ ~a ∈ ~a : ~a~n~n" (show-Γ Γ) (show-W¹ W_v) (show-W¹ W_c) ans))))

  ;; Check if value `W` satisfies predicate `p`
  (define (MΓ⊢oW [M : -M] [σ : -σ] [Γ : -Γ] [p : -o] . [Ws : -W¹ *]) : -R
    (define-values (Vs ts) (unzip-by -W¹-V -W¹-t Ws))
    (with-debugging/off
      ((R)
       (first-R (let ([Vs*
                       (for/list : (Listof -V) ([V (in-list Vs)] [t (in-list ts)])
                         (V+ σ V (predicates-of Γ t)))])
                  (apply loc:p∋Vs σ p Vs*))
                (let ()
                  (define Γ*
                    (for/fold ([Γ : -Γ Γ]) ([V (in-list Vs)] [t (in-list ts)] #:when t)
                      (match V
                        [(-● ps)
                         (for/fold ([Γ : -Γ Γ]) ([p (in-set ps)])
                           (Γ+ Γ (?t@ p t)))]
                        [(? -b? b)
                         (Γ+ Γ (-t.@ 'equal? (list t b)))]
                        [_ Γ])))
                  (MΓ⊢t M Γ* (apply ?t@ p ts)))))
      (when (and (equal? p 'char?)
                 (equal? Vs (list (-● (set 'eof-object? (-not/c 'eof-object?))))))
        (printf "~a ⊢ ~a ~a : ~a~n" (show-Γ Γ) (show-o p) (map show-W¹ Ws) R))))

  (define (MΓ+/-oW [M : -M] [σ : -σ] [Γ : -Γ] [o : -o] . [Ws : -W¹ *]) : (Values (Option -Γ) (Option -Γ))
    (define ss (map -W¹-t Ws))
    (Γ+/-R (apply MΓ⊢oW M σ Γ o Ws) Γ (apply ?t@ o ss)))

  ;; Check if `s` is provable in `Γ`
  (define (MΓ⊢t [M : -M] [Γ : -Γ] [t : -?t]) : -R
    (with-debugging/off
      ((R)
       (cond
         [t
          (match (Γ⊢t (-Γ-facts Γ) t)
            ['?

             ;; Heuristic avoiding calling out to solvers
             ;; However this heuristic is implemented should be safe in terms of soundness.
             ;; Not calling out to solver when should only hurts precision.
             ;; Calling out to solver when there's no need only hurts performance.
             (define should-call-smt?
               (match t
                 [(-t.@ h ts)
                  (define ts* (for/set: : (℘ -t) ([t ts] #:unless (-b? t)) t))
                  (define (difficult-h? [h : -h]) (memq h '(< > <= >= = equal? eq? eqv?)))
                  (and
                   (or (difficult-h? h)
                       #;(has-abstraction? t)
                       #;(for/or : Boolean ([φ (in-set (-Γ-facts Γ))])
                           (has-abstraction? φ)))
                   (for/or : Boolean ([φ (in-set (-Γ-facts Γ))])
                     (and (t-contains-any? φ ts*)
                          (or (has-abstraction? φ)
                              (match? φ (-t.@ (? difficult-h?) _))))))]
                 [_ #f]))

             #;(begin
                 (printf "should call? ~a~n" should-call-smt?)
                 (printf "M:~n")
                 (for ([(a As) M])
                   (printf "  * ~a ↦ ~a~n" (show-αₖ a) (set-map As show-ΓA)))
                 (printf "Γ: ~a~n" (show-Γ Γ))
                 (printf "-----------------------------------------~n")
                 (printf "~a~n~n" (show-t t)))

             (if should-call-smt? (ext-prove M Γ t) '?)]
            [R R])]
         [else '?]))
      (when s #;(match? s (-@ 'equal? _ _))
            (match-define (-Γ φs _ γs) Γ)
            (for ([φ φs]) (printf "~a~n" (show-t φ)))
            (for ([γ γs])
              (match-define (-γ _ blm? sₕ sₓs) γ)
              (printf "~a ; blm?~a~n" (show-s (apply ?t@ sₕ sₓs)) (and blm? #t)))
            (printf "-----------------------------------------~a~n" R)
            (printf "~a~n~n" (show-e s)))
      ))

  ;; Like `(Γ ⊓ s), V true` and `(Γ ⊓ ¬s), V false`, probably faster
  (define (Γ+/-V [M : -M] [Γ : -Γ] [V : -V] [t : -?t]) : (Values (Option -Γ) (Option -Γ))
    (with-debugging/off ((Γ₁ Γ₂) (Γ+/-R (first-R (loc:⊢V V) (MΓ⊢t M Γ t)) Γ t))
      (printf "Γ+/-V: ~a +/- ~a @ ~a~n - ~a~n - ~a~n~n"
              (show-Γ Γ)
              (show-V V)
              (show-t t)
              (and Γ₁ (show-Γ Γ₁))
              (and Γ₂ (show-Γ Γ₂)))))

  (define #:∀ (X) (MΓ+/-oW/handler [f₁ : (-Γ → (℘ X))]
                                   [f₂ : (-Γ → (℘ X))]
                                   [M : -M]
                                   [σ : -σ]
                                   [Γ : -Γ]
                                   [o : -o] .
                                   [Ws : -W¹ *]) : (℘ X)
    (define ss (map -W¹-t Ws))
    (case (apply MΓ⊢oW M σ Γ o Ws)
      [(✓) (f₁ Γ)]
      [(✗) (f₂ Γ)]
      [(?) (∪ (f₁ (Γ+ Γ (apply ?t@ o ss)))
              (f₂ (Γ+ Γ (?t@ 'not (apply ?t@ o ss)))))]))

  (define #:∀ (X) (MΓ⊢oW/handler [on-t : (→ (℘ X))]
                                 [on-f : (→ (℘ X))]
                                 [M : -M]
                                 [σ : -σ]
                                 [Γ : -Γ]
                                 [o : -o] .
                                 [Ws : -W¹ *]) : (℘ X)
    (case (apply MΓ⊢oW M σ Γ o Ws)
      [(✓) (on-t)]
      [(✗) (on-f)]
      [(?) (∪ (on-t) (on-f))]))

  (define #:∀ (X) (p∋Vs/handler [t : (→ (℘ X))]
                                [f : (→ (℘ X))]
                                [σ : -σ]
                                [o : -o] .
                                [Vs : -V *]) : (℘ X)
    (case (apply loc:p∋Vs σ o Vs)
      [(✓) (t)]
      [(✗) (f)]
      [(?) (∪ (t) (f))]))


  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
  ;;;;; Plausibility checking
  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (define (plausible-index? [M : -M] [σ : -σ] [Γ : -Γ] [W : -W¹] [i : Natural]) : Boolean
    (case (MΓ⊢oW M σ Γ 'integer? W)
      [(✓ ?)
       (define Wᵢ (let ([b (-b i)]) (-W¹ b b)))
       (case (MΓ⊢oW M σ Γ '= W Wᵢ)
         [(✗) #f]
         [else #t])]
      [else #f]))

  ;; Given `s`'s satisfiability in `Γ`, strengthen `Γ` both ways. `#f` represents a bogus path condition.
  (define (Γ+/-R [R : -R] [Γ : -Γ] [t : -?t]) : (Values (Option -Γ) (Option -Γ))
    (case R
      [(✓) (values (Γ+ Γ t) #f)]
      [(✗) (values #f       (Γ+ Γ (?t@ 'not t)))]
      [(?) (values (Γ+ Γ t) (Γ+ Γ (?t@ 'not t)))]))
  )
