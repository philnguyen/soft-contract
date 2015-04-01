#lang racket/base
(provide (all-defined-out))
(require redex/reduction-semantics racket/set racket/match
         "lib.rkt" "lang.rkt" "tc.rkt" "delta.rkt" "gen-term.rkt")

(define r₁
  (reduction-relation
   SCPCF #:domain ς
   [--> ((• T L) Σ)
        ((↓ T L) (++ Σ [L ↦ (• T)]))
        Opq₁
        (side-condition (term (∉ L (dom Σ))))]
   [--> ((• T L) Σ)
        ((↓ T L) Σ)
        Opq₂
        (side-condition (term (∈ L (dom Σ))))]
   [--> (V Σ)
        ((↓ T L) (++ Σ [L ↦ V]))
        Conc
        (side-condition (term (conc? V)))
        (where/hidden (T) ,(judgment-holds (⊢ₜ {} V T) T))
        (judgment-holds (∉dom L Σ {}))]
   [--> ((if (↓ ℤ L) E _) Σ)
        (E Σ_1)
        If-True
        (judgment-holds (δ Λ Σ zero? [L] 0 Σ_1))]
   [--> ((if (↓ ℤ L) _ E) Σ)
        (E Σ_1)
        If-False
        (judgment-holds (δ Λ Σ zero? [L] 1 Σ_1))]
   [--> ((O (↓ T_x L_x) ... L) Σ)
        ((↓ T L_a) (++ Σ_1 [L_a ↦ S]))
        Prim
        (judgment-holds (δ L Σ O [L_x ...] S Σ_1))
        #;(judgment-holds (Δ O [T_x ...] T))
        (where/hidden (T) ,(judgment-holds (Δ O [T_x ...] T) T))
        (judgment-holds (∉dom L_a Σ {}))]
   [--> ((O (↓ T_x L_x) ... L) Σ)
        (Err Σ_1)
        Prim-Err
        (judgment-holds (δ L Σ O [L_x ...] Err Σ_1))]
   [--> (((↓ (T → T′) L) (↓ T L_x)) Σ)
        ((// E X (↓ T L_x)) Σ)
        App-Lam
        (where (λ (X : T) E) (@ Σ L))]
   [--> (((↓ (ℤ → T) L) (↓ ℤ L_x)) Σ)
        ((↓ T L_a) (++ Σ [L_a ↦ (• T)] [L ↦ (case T [L_x ↦ L_a])]))
        App-Opq-Int
        (where (• _ ...) (@ Σ L))
        (judgment-holds (∉dom L_a Σ {}))]
   [--> (((↓ (T′ → T) L) (↓ (T_1 → T_2) L_x)) Σ)
        ((↓ T L_a) (++ Σ [L_a ↦ (• T)] [L ↦ (λ (X : T′) (↓ T L_a))]))
        App-Opq-Const
        (where (• _ ...) (@ Σ L))
        (judgment-holds (∉dom L_a Σ {}))]
   [--> (((↓ (T′ → T) L) (↓ T′ L_x)) Σ)
        ((// V X (↓ T′ L_x)) (++ Σ [L ↦ (λ (X : T′) V)] [L_1 ↦ (• (T′ → T))]))
        App-Opq-Clo
        (where (• _ ...) (@ Σ L))
        (where (T_1 → T_2) T′)
        (where (T_3 → T_4) T)
        (judgment-holds (∉dom L_1 Σ {}))
        (where Y (+X T_3))
        (where X ,(variable-not-in (term Y) (term (+X T′))))
        (where V (λ (Y : T_3) (((↓ (T′ → T) L_1) X) Y)))]
   [--> (((↓ (T′ → T) L) (↓ T′ L_x)) Σ)
        (((↓ (T_2 → T) L_2) ((↓ T′ L_x) (↓ T_1 L_1))) (++ Σ [L ↦ V] [L_1 ↦ (• T_1)] [L_2 ↦ (• (T_2 → T))]))
        App-Havoc
        (where (• _ ...) (@ Σ L))
        (where (T_1 → T_2) T′)
        (judgment-holds (∉dom L_1 Σ {}))
        (judgment-holds (∉dom L_2 Σ {L_1}))
        (where X (+X T′))
        (where V (λ (X : T′) ((↓ (T_2 → T) L_2) (X (↓ T_1 L_1)))))]
   [--> (((↓ (ℤ → T) L) (↓ ℤ L_x)) Σ)
        ((↓ T L_a) Σ)
        App-Case₁
        (where (case T _ ... [L_x ↦ L_a] _ ...) (@ Σ L))]
   [--> (((↓ (ℤ → T) L) (↓ ℤ L_x)) Σ)
        ((↓ T L_a) (++ Σ [L ↦ (case T [L_z ↦ L_b] ... [L_x ↦ L_a])] [L_a ↦ (• T)]))
        App-Case₂
        (where (case T [L_z ↦ L_b] ...) (@ Σ L))
        (side-condition (term (∉ L_x (L_z ...))))
        (judgment-holds (∉dom L_a Σ {}))]))

(define →₁ ; Context closure of `r₁`
  (reduction-relation
   SCPCF #:domain ς
   [--> ((in-hole C E) Σ) ((in-hole C E_1) Σ_1)
        (computed-name (term any_name))
        (where {_ ... (any_name (E_1 Σ_1)) _ ...}
               ,(apply-reduction-relation/tag-with-names r₁ (term (E Σ))))]
   [--> ((in-hole C Err) Σ) (Err Σ)
        Err
        (side-condition (not (hole? (term C))))]))

(define (@r₁ s) (apply-reduction-relation r₁ s))
(define (@→₁ s) (apply-reduction-relation →₁ s))

(module+ test
  (require rackunit racket/contract)

  ;; Progress and preservation
  (define/contract (check-p/p ς T)
    (ς? T? . -> . (listof ς?))
    (match-define `(,E ,_) ς)
    (match E
      [`(↓ ,T′ ,_) (check-equal? T′ T) '()]
      [E
       (define ςs (apply-reduction-relation →₁ ς))
       (when (null? ςs)
         (printf "~a reduces to nothing~n" ς))
       (check-false (null? ςs))
       (for/list ([ς′ (in-list ςs)]
             #:unless (redex-match? SCPCF ((in-hole C Err) _) ς′))
         (match-define `(,E′ ,_) ς′)
         (check-equal? (term (tc ,E′)) T)
         ς′)]))

  (define (→₁/tc E [depth 50])
    (define T (term (tc ,E)))
    (define ς (term (,E {})))
    (test-case (format "~a : ~a" E T)
      (void
       (for/fold ([ςs (list ς)]) ([i (in-range depth)] #:break (null? ςs))
         (for*/list ([ς (in-list ςs)] [ς′ (in-list (check-p/p ς T))])
           ς′)))))

  (→₁/tc 42)
  (→₁/tc '(+ 1 2 Λ))
  (→₁/tc '(λ (x : ℤ) x))
  (→₁/tc '(/ 1 (- 100 ((• (ℤ → ℤ) g) (• ℤ n)) Λ) Λ))
  (→₁/tc '(((• ((ℤ → ℤ) → (ℤ → ℤ)) f) (λ (n : ℤ) (if (= n 0 Λ) 100 0))) 0))
  (→₁/tc
    (term (LET* ([f (λ (g : (ℤ → ℤ))
                      (λ (n : ℤ)
                        (/ 1 (- 100 (g n) L-) L/)))])
                ((λ (f : ((ℤ  → ℤ) → (ℤ → ℤ)))
                   ((f (λ (n : ℤ)
                         (if (= n 0 L=) 100 0)))
                    0))
                 f))))
  (→₁/tc
    (term (LET* ([f (λ (g : (ℤ → ℤ))
                      (λ (n : ℤ)
                        (/ 1 (- 100 (g n) L-) L/)))])
                ((• (((ℤ  → ℤ) → (ℤ → ℤ)) → ℤ) L•) f))))


  (redex-check
   SCPCF T
   (begin
     (define Es (gen/T (term T)))
     (printf "Executing ~a terms of type ~a~n" (length Es) (term T))
     (for ([E (in-list Es)])
       (→₁/tc E 100)))
   #:attempts 20))


