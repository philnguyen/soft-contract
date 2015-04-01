#lang racket/base
(provide ce)
(require redex racket/set racket/match racket/contract
         "lib.rkt" "lang.rkt" "tc.rkt" "reduction.rkt" "z3.rkt")

;; Instantiate an abstract heap
(define-metafunction SCPCF
  model : Σ -> Σ or #f
  [(model Σ) (model/Σ Σ_1)
   ;;(where _ ,(printf "model: Σ_1: ~a~n" (term (model/z3 Σ))))
   (where Σ_1 (model/z3 Σ))]
  [(model Σ) #f
   (where #f (model/z3 Σ))])

;; Construct a concrete value at location `L`
(define-metafunction SCPCF
  construct : Σ L -> V
  [(construct (name Σ {_ ... [L ↦ n] _ ...}) L) n]
  [(construct (name Σ {_ ... [L ↦ (λ (X : T) E)] _ ...}) L)
   (λ (X : T) (construct/E Σ E))]
  [(construct (name Σ {_ ... [L ↦ (case T [L_x ↦ L_a] ...)] _ ...}) L)
   (λ (x : T) (construct/cases x Σ ([L_x ↦ L_a] ...)))])

;; Fully instantiate expression `E`
(define-metafunction SCPCF
  construct/E : Σ E -> E
  [(construct/E Σ (if E ...)) (if (construct/E Σ E) ...)]
  [(construct/E Σ (O E ... L)) (O (construct/E Σ E) ... L)]
  [(construct/E Σ (λ (X : T) E)) (λ (X : T) (construct/E Σ E))]
  [(construct/E Σ ((• T L) E_x)) (construct/E Σ E_x)
   (where (• _ ...) (@ Σ L))]
  [(construct/E Σ ((↓ T L) E_x)) (construct/E Σ E_x)
   (where (• _ ...) (@ Σ L))]
  [(construct/E Σ (E_f E_x)) E 
   (where E_f* (construct/E Σ E_f))
   (where E_x* (construct/E Σ E_x))
   (where E ,(if (term (inlinable? E_f* E_x*))
                 (term (inline E_f* E_x*))
                 (term (E_f* E_x*))))]
  [(construct/E Σ (↓ T L)) (construct Σ L)]
  [(construct/E Σ E) E])

(define-relation SCPCF
  inlinable? ⊆ E × E
  [(inlinable? (λ (X : ℤ) _) n)]
  [(inlinable? (λ (X : ℤ) _) Z)]
  [(inlinable? (λ (X : _) E) _)
   (side-condition (<= (term (count-X X E)) 1))])

(define-metafunction SCPCF
  inline : (λ (X : T) E) E -> E
  [(inline (λ (X : _) E) E_1) (// E X E_1)])

;; Construct conditionals for mappings
(define-metafunction SCPCF
  construct/cases : X Σ ([L ↦ L] ...) -> E
  [(construct/cases X Σ ()) 0]
  [(construct/cases X Σ {[_ ↦ L]}) (construct Σ L)]
  [(construct/cases X Σ {[L_x ↦ L_a] any ...})
   (if (= X (construct Σ L_x) Λ) (construct Σ L_a)
       (construct/cases X Σ {any ...}))])

(define/contract (ce E [depth 1000])
  ((E?) (integer?) . ->* . (or/c 'safe 'timeout ς? (list/c any/c #f)))
  (define ς (term (,E {})))
  (define Ls (list->set (term (labs ,E))))
  (define (concrete? L) (set-member? Ls L))
  (define ans
    (for/fold ([ςs (list ς)]) ([i (in-range depth)] #:break (ς? ςs))
      (for*/fold ([acc null]) ([ς (in-list ςs)]
                               [ς′ (in-list (apply-reduction-relation →₁ ς))]
                               #:break (ς? acc))
        (match ς′
          [`((err ,(? concrete? L) ,_) ,_) ς′]
          [_ (cons ς′ acc)]))))
  (match ans
    [(list) 'safe]
    [`((err ,L ,O) ,Σ)
     (define !Σ (term (model ,Σ)))
     (define !Σ_ce (for/list ([L (in-list (term (holes ,E)))])
                     (term [,L ↦ (construct ,!Σ ,L)])))
     `((err ,L ,O) ,!Σ_ce)]
    [_ 'timeout]))

(module+ test
  
  (ce (term ((• ((ℤ → ℤ) → ℤ) ◆)
             (λ (x : ℤ) (/ 1 x p)))))
  (ce (term (LET* ([f (λ (g : (ℤ → ℤ))
                        (λ (n : ℤ)
                          (/ 1 (- 100 (g n) ℓ₁) ℓ₂)))])
                  ((• (((ℤ → ℤ) → (ℤ → ℤ)) → ℤ) ●₁) f))))
  (ce (term (+ 1 (• ℤ ●) Λ)))

  ;; TODO: example query + model generated from this
  (ce (term (LET* ([f (• (ℤ → (ℤ → ℤ)) Lf)]
                   [a (• ℤ La)]
                   [b (• ℤ Lb)]
                   [c (• ℤ Lc)])
                  (if (= a b ℓ₁)
                      (/ 1
                         (+ 1
                            (* ((f a) c)
                               ((f b) c)
                               ℓ₃)
                            ℓ₄)
                         ℓ₂)
                      42))))) 
