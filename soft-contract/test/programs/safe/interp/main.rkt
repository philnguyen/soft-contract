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

(provide
 (contract-out
  [struct App ([fun Exp/c] [arg Exp/c])]
  [struct Lam ([var Var?] [body Exp/c])]
  [struct If0 ([cnd Exp/c] [thn Exp/c] [els Exp/c])]
  [ev (Exp/c Env/c . -> . Val/c)]))
