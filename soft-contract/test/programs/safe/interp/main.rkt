#lang racket/base

(require racket/contract
         racket/match)

;; Syntax
(struct App (fun arg) #:transparent)
(struct Lam (var body) #:transparent)
(struct If0 (cnd thn els) #:transparent)
(define prim? (or/c 'add1 'integer? 'procedure?))
(define Var? symbol?)
(define Lit/c (or/c Lam? integer? prim?))
(define Exp/c (or/c Lit/c Var? App? If0?))
;; Semanics
(struct Clo (var body env) #:transparent)
(define Val/c (or/c Clo? integer? prim?))
(define Env/c (listof (cons/c Var? Val/c)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Big-step
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define (evl e) (ev e '()))

(define/contract (ev e ρ)
  (Exp/c Env/c . -> . Val/c)
  (match e
    [(Lam x e) (Clo x e ρ)]
    [(? integer? i) i]
    [(? prim? p) p]
    [(? Var? x) (cond [(assoc x ρ) => cdr]
                      [else (error 'lookup)])]
    [(App f x) (ap (ev f ρ) (ev x ρ))]
    [(If0 e₀ e₁ e₂) (ev (if (equal? 0 (ev e₀ ρ)) e₁ e₂) ρ)]))

(define/contract (ap f v)
  (Val/c Val/c . -> . Val/c)
  (match f
    [(Clo x e ρ) (ev e (cons (cons x v) ρ))]
    [(? prim? p) (δ p v)]
    [(? integer? i) (error 'ap)]))

(define/contract (δ o v)
  (prim? Val/c . -> . Val/c)
  (case o
    [(add1) (if (integer? v) (add1 v) (error 'add1))]
    [(integer?) (if (integer? v) 0 1)]
    [(procedure?) (if (or (Clo? v) (prim? v)) 0 1)]
    [else (error 'δ)]))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; CEK machine
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(struct S (kont) #:transparent)
(struct S:ev S (ctrl env) #:transparent)
(struct S:co S (val) #:transparent)
(struct S:ans (val) #:transparent)
(struct K () #:transparent)
(struct K:mt K () #:transparent)
(struct K:fn K (arg env rest) #:transparent)
(struct K:ar K (fun rest) #:transparent)
(struct K:if K (thn els env rest) #:transparent)

(define S/c (or/c S:ev? S:co?))
(define S*/c (or/c S/c S:ans?))

(define/contract step
  (S/c . -> . S*/c)
  (match-lambda
    [(S:ev k e ρ)
     (match e
       [(Lam x e)      (S:co k (Clo x e ρ))]
       [(? integer? i) (S:co k i)]
       [(? prim? p)    (S:co k p)]
       [(? Var? x)     (S:co k (cond [(assoc x ρ) => cdr]
                                     [else (error 'lookup)]))]
       [(App f x)      (S:ev (K:fn x ρ k) f ρ)]
       [(If0 e₀ e₁ e₂) (S:ev (K:if e₁ e₂ ρ k) e₀ ρ)])]
    [(S:co k V)
     (match k
       [(K:mt) (S:ans V)]
       [(K:fn x ρ k) (S:ev (K:ar V k) x ρ)]
       [(K:ar f k) (match f
                     [(Clo x e ρ) (S:ev k e (cons (cons x V) ρ))]
                     [(? prim? p) (S:co k (δ p V))]
                     [(? integer?) (error 'ap)])]
       [(K:if e₁ e₂ ρ k) (S:ev k (if (equal? V 0) e₁ e₂) ρ)])]))

(define/contract (ev/step e)
  (Exp/c . -> . Val/c)
  (define (inj e) (S:ev (K:mt) e '()))
  (let run ([S (inj e)])
    (match (step S)
      [(S:ans V) V]
      [S* (run S*)])))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Compile then run
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define (evl/comp e) ((comp e) '()))

;; Value representation in the meta-language
(define ⟦Val⟧/c (or/c integer?
                      prim?
                      ((recursive-contract ⟦Val⟧/c #:chaperone)
                       . -> .
                       (recursive-contract ⟦Val⟧/c #:chaperone))))
(define ⟦Env⟧/c (listof (cons/c Var? ⟦Val⟧/c)))
(define/contract comp
  (Exp/c . -> . (⟦Env⟧/c . -> . ⟦Val⟧/c))
  (match-lambda
    [(Lam x e)      (define ⟦e⟧ (comp e))
                    (λ (ρ) (λ (v) (⟦e⟧ (cons (cons x v) ρ))))]
    [(? integer? i) (λ _ i)]
    [(? prim? p)    (λ _ p)]
    [(? Var? x)     (λ (ρ) (cond [(assoc x ρ) => cdr]
                                 [else (error 'lookup)]))]
    [(App f x)      (define ⟦f⟧ (comp f))
                    (define ⟦x⟧ (comp x))
                    (λ (ρ)
                      (define v₁ (⟦f⟧ ρ))
                      (define v₂ (⟦x⟧ ρ))
                      (match v₁
                        [(? procedure? f) (f v₂)]
                        [(? prim? p)
                         (case p
                           [(add1) (if (integer? v₂) (add1 v₂) (error 'add1))]
                           [(integer?) (if (integer? v₂) 0 1)]
                           [(procedure?) (if (or (procedure? v₂) (prim? v₂)) 0 1)]
                           [else (error 'δ)])]
                        [(? integer?) (error 'ap)]))]
    [(If0 e₀ e₁ e₂) (define ⟦e₀⟧ (comp e₀))
                    (define ⟦e₁⟧ (comp e₁))
                    (define ⟦e₂⟧ (comp e₂))
                    (λ (ρ)
                      ((if (equal? (⟦e₀⟧ ρ) 0) ⟦e₁⟧ ⟦e₂⟧) ρ))]))

(provide
 (contract-out
  [struct App ([fun Exp/c] [arg Exp/c])]
  [struct Lam ([var Var?] [body Exp/c])]
  [struct If0 ([cnd Exp/c] [thn Exp/c] [els Exp/c])]
  [evl (Exp/c . -> . Val/c)]
  [ev/step (Exp/c . -> . Val/c)]
  [evl/comp (Exp/c . -> . ⟦Val⟧/c)]))
