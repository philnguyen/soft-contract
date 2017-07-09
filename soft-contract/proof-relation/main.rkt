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
         "../runtime/signatures.rkt"
         "../signatures.rkt"
         "signatures.rkt"

         "widen.rkt"
         "ext.rkt"
         "local.rkt")

(define-unit pre-proof-system@
  (import (prefix local: local-prover^) external-prover^ widening^ pc^)
  (export proof-system^)
  
  ;; Check if value satisfies (flat) contract
  (define (Γ⊢V∈C [σ : -σ] [Γ : -Γ] [W_v : -W¹] [W_c : -W¹]) : -R
    (match-define (-W¹ V v) W_v)
    (match-define (-W¹ C c) W_c)
    (with-debugging/off
      ((ans)
       (first-R (local:p∋Vs σ C (V+ σ V (predicates-of Γ v)))
                (match V
                  [(-● ps)
                   (define Γ*
                     (for/fold ([Γ : -Γ Γ]) ([p ps])
                       (Γ+ Γ (?t@ p v))))
                   (Γ⊢t Γ* (and (-h? c) (?t@ c v)))]
                  [_ (Γ⊢t Γ (and (-h? c) (?t@ c v)))])))
      (when (and (-Clo? V))
        (printf "~a ⊢ ~a ∈ ~a : ~a~n~n" (show-Γ Γ) (show-W¹ W_v) (show-W¹ W_c) ans))))

  ;; Check if value `W` satisfies predicate `p`
  (define (Γ⊢oW [σ : -σ] [Γ : -Γ] [p : -o] . [Ws : -W¹ *]) : -R
    (define-values (Vs ts) (unzip-by -W¹-V -W¹-t Ws))
    (with-debugging/off
      ((R)
       (first-R (let ([Vs*
                       (for/list : (Listof -V) ([V (in-list Vs)] [t (in-list ts)])
                         (V+ σ V (predicates-of Γ t)))])
                  (apply local:p∋Vs σ p Vs*))
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
                  (Γ⊢t Γ* (apply ?t@ p ts)))))
      (when (and (equal? p 'char?)
                 (equal? Vs (list (-● (set 'eof-object? (-not/c 'eof-object?))))))
        (printf "~a ⊢ ~a ~a : ~a~n" (show-Γ Γ) (show-o p) (map show-W¹ Ws) R))))

  (define (Γ+/-oW [σ : -σ] [Γ : -Γ] [o : -o] . [Ws : -W¹ *]) : (Values (Option -Γ) (Option -Γ))
    (define ss (map -W¹-t Ws))
    (Γ+/-R (apply Γ⊢oW σ Γ o Ws) Γ (apply ?t@ o ss)))

  ;; Check if `s` is provable in `Γ`
  (define (Γ⊢t [Γ : -Γ] [t : -?t]) : -R
    (with-debugging/off
      ((R)
       (cond
         [t
          (match (local:Γ⊢t (-Γ-facts Γ) t)
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

             (if should-call-smt? (ext-prove Γ t) '?)]
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
  (define (Γ+/-V [Γ : -Γ] [V : -V] [t : -?t]) : (Values (Option -Γ) (Option -Γ))
    (with-debugging/off ((Γ₁ Γ₂) (Γ+/-R (first-R (local:⊢V V) (Γ⊢t Γ t)) Γ t))
      (printf "Γ+/-V: ~a +/- ~a @ ~a~n - ~a~n - ~a~n~n"
              (show-Γ Γ)
              (show-V V)
              (show-t t)
              (and Γ₁ (show-Γ Γ₁))
              (and Γ₂ (show-Γ Γ₂)))))

  (define #:∀ (X) (Γ+/-oW/handler [f₁ : (-Γ → (℘ X))]
                                  [f₂ : (-Γ → (℘ X))]
                                  [σ : -σ]
                                  [Γ : -Γ]
                                  [o : -o] .
                                  [Ws : -W¹ *]) : (℘ X)
    (define ss (map -W¹-t Ws))
    (case (apply Γ⊢oW σ Γ o Ws)
      [(✓) (f₁ Γ)]
      [(✗) (f₂ Γ)]
      [(?) (∪ (f₁ (Γ+ Γ (apply ?t@ o ss)))
              (f₂ (Γ+ Γ (?t@ 'not (apply ?t@ o ss)))))]))

  (define #:∀ (X) (Γ⊢oW/handler [on-t : (→ (℘ X))]
                                [on-f : (→ (℘ X))]
                                [σ : -σ]
                                [Γ : -Γ]
                                [o : -o] .
                                [Ws : -W¹ *]) : (℘ X)
    (case (apply Γ⊢oW σ Γ o Ws)
      [(✓) (on-t)]
      [(✗) (on-f)]
      [(?) (∪ (on-t) (on-f))]))

  (: p∋Vs/handler (∀ (X) (→ (℘ X)) (→ (℘ X)) -σ -o -V * → (℘ X)))
  (define (p∋Vs/handler t f σ o . Vs)
    (case (apply local:p∋Vs σ o Vs)
      [(✓) (t)]
      [(✗) (f)]
      [(?) (∪ (t) (f))]))


  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
  ;;;;; Plausibility checking
  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (define (plausible-index? [σ : -σ] [Γ : -Γ] [W : -W¹] [i : Natural]) : Boolean
    (case (Γ⊢oW σ Γ 'integer? W)
      [(✓ ?)
       (define Wᵢ (let ([b (-b i)]) (-W¹ b b)))
       (case (Γ⊢oW σ Γ '= W Wᵢ)
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

(define-compound-unit/infer proof-system@
  (import prims^ for-gc^ pc^ sto^ val^ pretty-print^ env^)
  (export proof-system^ widening^ local-prover^)
  (link local-prover@ external-prover@ widening@ pre-proof-system@))
