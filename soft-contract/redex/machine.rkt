#lang racket/base
(require racket/match racket/set racket/list racket/function racket/contract redex
         "lib.rkt" "syntax.rkt" "provability.rkt" "delta.rkt")

(define (→/ς ds)
  (reduction-relation
   L #:domain ς

   ;; Bases
   [--> ({b _}   Γ σ τ Ξ M)
        ({b @ b} Γ σ τ Ξ M)
        Base]
   [--> ({(λ (x) e) ρ}                 Γ σ τ Ξ M)
        ({(Clo x e ρ* Γ*) @ (λ (x) e)} Γ σ τ Ξ M)
        Clo
        (where (ρ* Γ*) (restrict e ρ Γ))]
   [--> ({• _}    Γ σ τ Ξ M)
        ((● @ #f) Γ σ τ Ξ M)
        Opq]
   [--> ({x ρ}   Γ σ τ Ξ M)
        ({V @ x} Γ σ τ Ξ M)
        Var
        (judgment-holds (∈ V (lookup σ (lookup ρ x))))
        (where #f (spurious? x V Γ))]
   [--> ({(ref x) _} Γ σ τ  Ξ M)
        ({v ⊥}       ∅ σ τ* Ξ* M)
        Ref
        (where {_ ... (def x v) _ ...} ,ds)
        (where τ* (v ⊥ ∅))
        (where Ξ* (MM⊔ Ξ [τ* ↦ ((rt Γ (ref x)) τ)]))]

   ;; Pushes
   [--> ({(e_f e_x) ρ} Γ σ τ  Ξ  M)
        ({e_f       ρ} Γ σ τ* Ξ* M)
        App-Push
        ;; continue executing with `Γ` b/c i don't wanna drop it,
        ;; but `Γ_f` is enough for the stack address
        (where τ* (-τ e_f ρ Γ))
        (where Ξ* (MM⊔ Ξ [τ* ↦ ((fn e_x ρ) τ)]))]
   [--> ({(o e_1 e ...) ρ} Γ σ τ  Ξ  M)
        ({e_1           ρ} Γ σ τ* Ξ* M)
        Op-Push
        (where τ* (-τ e_1 ρ Γ))
        (where Ξ* (MM⊔ Ξ [τ* ↦ ((o [] [e ...] ρ) τ)]))]
   [--> ({(if e_0 e_1 e_2) ρ} Γ σ τ  Ξ  M)
        ({e_0              ρ} Γ σ τ* Ξ* M)
        If-Push
        (where τ* (-τ e_0 ρ Γ))
        (where Ξ* (MM⊔ Ξ [τ* ↦ ((if e_1 e_2 ρ) τ)]))]
   [--> ({(set! x e) ρ} Γ σ τ  Ξ  M)
        ({        e  ρ} Γ σ τ* Ξ* M)
        Set!-Push
        (where τ* (-τ e ρ Γ))
        (where Ξ* (MM⊔ Ξ [τ* ↦ ((set! (lookup ρ x)) τ)]))]

   ;; Swaps
   [--> (W       Γ σ τ  Ξ  M )
        ([e_x ρ] Γ σ τ* Ξ* M*)
        App-Swap
        (judgment-holds (∈ ((fn e_x ρ) τ**) (lookup Ξ τ)))
        (where τ* (-τ e_x ρ Γ))
        (where Ξ* (MM⊔ Ξ [τ* ↦ ((ar W) τ**)]))
        (where (e_τ _ _) τ)
        (where (_ @ ?e) W)
        (where M* (MM⊔ M [e_τ ↦ (?e Γ)]))]
   [--> (W       Γ σ τ  Ξ  M )
        ({e_i ρ} Γ σ τ* Ξ* M*)
        Op-Swap
        (judgment-holds (∈ ((o [W_1 ...] [e_i e ...] ρ) τ**) (lookup Ξ τ)))
        (where τ* (-τ e_i ρ Γ))
        (where Ξ* (MM⊔ Ξ [τ* ↦ ((o [W_1 ... W] [e ...] ρ) τ**)]))
        (where (e_τ _ _) τ)
        (where (_ @ ?e) W)
        (where M* (MM⊔ M [e_τ ↦ (?e Γ)]))]
   
   ;; (Pop + Return)s
   [--> ({V @ ?e_x} Γ  σ  τ  Ξ  M )
        ({e* ρ*}    Γ* σ* τ* Ξ* M*)
        App-β
        (judgment-holds (∈ ((ar ((Clo x e* ρ Γ*) @ ?e_f)) τ**) (lookup Ξ τ)))
        (where α (-α.bind x ?e_x Γ))
        (where σ* (MM⊔ σ [α ↦ V]))
        (where ρ* (++ ρ [x ↦ α]))
        (where τ* (-τ e* ρ* Γ*))
        (where Ξ* (MM⊔ Ξ [τ* ↦ ((rt Γ (@* ?e_f ?e_x)) τ**)]))
        (where (e_τ _ _) τ)
        (where M* (MM⊔ M [e_τ ↦ (?e_x Γ)]))]
   [--> ((name W (_ @ ?e)) Γ   σ   τ  Ξ M )
        ({V @ ?e_a}        Γ_a σ_a τ* Ξ M*)
        Op-Pop
        (judgment-holds (∈ ((o [W_1 ...] [] _) τ*) (lookup Ξ τ)))
        (judgment-holds (δ σ Γ o [W_1 ... W] σ_a Γ_a V))
        (where ((_ @ ?e*) ...) (W_1 ... W))
        (where ?e_a (o* o ?e* ...))
        (where #f (spurious? ?e_a V Γ_a))
        (where (e_τ _ _) τ)
        (where M* (MM⊔ M [e_τ ↦ (?e Γ)]))]
   [--> ((name W (_ @ ?e)) Γ   σ   τ  Ξ M )
        (err               Γ_a σ_a τ* Ξ M*)
        Op-Err
        (judgment-holds (∈ ((o [W_1 ...] [] _) τ*) (lookup Ξ τ)))
        (judgment-holds (δ σ Γ o [W_1 ... W] σ_a Γ_a err))
        (where ((_ @ ?e*) ...) (W_1 ... W))
        (where (e_τ _ _) τ)
        (where M* (MM⊔ M [e_τ ↦ (?e Γ)]))]
   [--> ((name W (_ @ ?e)) Γ  σ τ  Ξ  M )
        ({e* ρ}            Γ* σ τ* Ξ* M*)
        If-True
        (judgment-holds (∈ ((if e* _ ρ) τ**) (lookup Ξ τ)))
        (judgment-holds (split Γ W #t Γ*))
        (where (e_τ _ _) τ)
        (where M* (MM⊔ M [e_τ ↦ (?e Γ)]))
        (where τ* (-τ e* ρ Γ*))
        (where Ξ* (MM⊔ Ξ [τ* ↦ (tail τ**)]))]
   [--> ((name W (_ @ ?e)) Γ  σ τ  Ξ  M )
        ({e* ρ}            Γ* σ τ* Ξ* M*)
        If-False
        (judgment-holds (∈ ((if _ e* ρ) τ**) (lookup Ξ τ)))
        (judgment-holds (split Γ W #f Γ*))
        (where (e_τ _ _) τ)
        (where M* (MM⊔ M [e_τ ↦ (?e Γ)]))
        (where τ* (-τ e* ρ Γ*))
        (where Ξ* (MM⊔ Ξ [τ* ↦ (tail τ**)]))]
   [--> ((name W {V @ ?e  }) Γ   σ τ  Ξ M )
        (        {V @ ?e_0}  Γ_0 σ τ* Ξ M*)
        Rt
        (judgment-holds (∈ ((rt Γ_0 ?e_0) τ*) (lookup Ξ τ)))
        (where #f (spurious? ?e_0 V Γ_0))
        (where (e_τ _ _) τ)
        (where M* (MM⊔ M [e_τ ↦ (?e Γ)]))]
   [--> ((name W {V @ ?e}) Γ σ  τ  Ξ M )
        (        {1 @ #f}  Γ σ* τ* Ξ M*)
        Set!-Pop
        (judgment-holds (∈ ((set! α) τ*) (lookup Ξ τ)))
        (where σ* (MM⊔ σ [α ↦ V]))
        (where (e_τ _ _) τ)
        (where M* (MM⊔ M [e_τ ↦ (?e Γ)]))]
   [--> ((name W (_ @ ?e)) Γ σ τ  Ξ M )
        (      W           Γ σ τ* Ξ M*)
        Tail
        (judgment-holds (∈ (tail τ*) (lookup Ξ τ)))
        (where (e_τ _ _) τ)
        (where M* (MM⊔ M [e_τ ↦ (?e Γ)]))]

   ;; Hack
   [--> ((name W (V @ ?e)) Γ σ τ  Ξ M )
        ((V @ #f)          ∅ σ #f Ξ M*)
        Halt
        (side-condition (set-empty? (term (lookup Ξ τ))))
        (where (e_τ _ _) τ)
        (where M* (MM⊔ M [e_τ ↦ (?e Γ)]))]
   [--> (err Γ σ τ  Ξ M )
        (err ∅ σ #f Ξ M*)
        Halt-Err
        (where (e_τ _ _) τ)
        (where M* (MM⊔ M [e_τ ↦ (err Γ)]))]))

(define (→/ξ ds)
  (define → (→/ς ds))
  (reduction-relation
   L #:domain ξ
   [--> (Cs  σ  Ξ  M )
        (Cs* σ* Ξ* M*)
        (where ςs
               ,(for/fold ([ςs {set}]) ([C (in-set (term Cs))])
                  (match-define `(,E ,Γ ,τ) C)
                  (set-union ςs (list->set (apply-reduction-relation → (term (,E ,Γ σ ,τ Ξ M)))))))
        (where (Cs* σ* Ξ* M*)
               ,(let ()
                  (define-values (Cs* σ* Ξ* M*)
                    (for/fold ([Cs* (term Cs)] [σ* (term σ)] [Ξ* (term Ξ)] [M* (term M)])
                              ([ς (in-set (term ςs))])
                      (match-define `(,E ,Γ ,σ ,τ ,Ξ ,M) ς)
                      (values (set-add Cs* (term (,E ,Γ ,τ)))
                              (term (⊔ ,σ* ,σ))
                              (term (⊔ ,Ξ* ,Ξ))
                              (term (⊔ ,M* ,M)))))
                  (list Cs* σ* Ξ* M*)))
        ;; need this condition for `apply-reduction-relation*` to give something
        (side-condition (not (and (equal? (term Cs) (term Cs*))
                                  (equal? (term σ ) (term σ* ))
                                  (equal? (term Ξ ) (term Ξ* ))
                                  (equal? (term M ) (term M* )))))]))

;; Restrict environments before making stack address
(define-metafunction L
  -τ : e ρ Γ -> τ
  ;; treat `(ref x)` and `(e e)` specially due to implicit `(rt _)`
  [(-τ (ref x) ρ Γ) ((ref x) ⊥ Γ)]
  [(-τ (e_1 e_2) ρ Γ) ((e_1 e_2) ρ* Γ)
   (where (ρ* _) (restrict (e_1 e_2) ρ Γ))]
  [(-τ e ρ Γ) (e ρ* Γ*)
   (where (ρ* Γ*) (restrict e ρ Γ))])

(define-metafunction L
  -α.bind : x ?e Γ -> α
  [(-α.bind x #f _) x]
  [(-α.bind x e Γ) (x e Γ*)
   (where (_ Γ*) (restrict e ⊥ Γ))])

;; inject program to initial state
(define-metafunction L
  𝑰/ς : e -> ς
  [(𝑰/ς e)
   ([e ⊥] ∅ ⊥ τ {M+ [τ ↦ ∅]} ⊥)
   (where τ (e ⊥ ∅))])
(define-metafunction L
  𝑰/ξ : e -> ξ
  [(𝑰/ξ e)
   ({S+ ((e ⊥) ∅ τ)} ⊥ {M+ [τ ↦ ∅]} ⊥)
   (where τ (e ⊥ ∅))])

(define-syntax-rule (pviz/ς p)
  (match-let ([`(,ds (... ...) ,e) (term p)])
    (traces (→/ς ds) (term (𝑰/ς ,e)))))
(define-syntax-rule (pviz/ξ p)
  (match-let ([`(,ds (... ...) ,e) (term p)])
    (traces (→/ξ ds) (term (𝑰/ξ ,e)))))
(define-syntax-rule (pev/ς p)
  (match-let ([`(,ds (... ...) ,e) (term p)])
    (list->set (apply-reduction-relation* (→/ς ds) (term (𝑰/ς ,e)) #:cache-all? #t))))
(define-syntax-rule (pev/ξ p)
  (match-let ([`(,ds (... ...) ,e) (term p)])
    (match-define `{(,Cs ,σ ,Ξ ,M)}
      (apply-reduction-relation* (→/ξ ds) (term (𝑰/ξ ,e)) #:cache-all? #t))
    (values Cs σ Ξ M)))
(define-syntax-rule (viz/ς e) (pviz/ς (e)))
(define-syntax-rule (viz/ξ e) (pviz/ξ (e)))
(define-syntax-rule (ev/ς e) (pev/ς (e)))
(define-syntax-rule (ev/ξ e) (pev/ξ (e)))

(define-syntax-rule (optimize p)
  (let ()
    (match-define `(,ds (... ...) ,e) (term p)) ; duplicate use of `p`. Be careful.
    (define-values (Cs σ Ξ M) (pev/ξ p))
    (append (for/list ([d (in-list ds)])
              (term (opt-d ,M ,d)))
            (list (term (opt-e ,M ,e))))))

(define-metafunction L
  opt-d : M d -> d
  [(opt-d M (def x v_c v)) (def x (opt-e M v_c) (opt-e M v))])
; TODO: opt-e

(define-term t₁ (add1 (add1 2)))
(define-term t₂ ((λ (x) (add1 x)) 42))
(define-term t₃ (LET* ([f (λ (x) (cons? x))] [v •]) (if (f v) (car v) 42)))
(define-term t₄ (LET* ([id (λ (x) x)]
                       [y (id 1)]
                       [z (id 0)])
                  z))
(define-term p₁
  ((def inc (λ (n) (add1 n)))
   (def opq •)
   ((ref inc) (ref opq))))
(define-term p₂
  ((def f (λ (x) ((λ (n) (add1 1)) x)))
   (def x •)
   (f x)))
(define-term p₃
  ((def list?
     (λ (x)
       (if (not x) 1
           (AND (cons? x) ((ref list?) (cdr x))))))
   #;(def rev
     (λ (l)
       (λ (ac)
         (if (not l) ac
             (((ref rev) (cdr l)) (cons (car l) ac))))))
   (def opq •)
   ((ref list?) (ref opq))
   #;(if ((ref list?) (ref opq))
       (((ref rev  ) (ref opq)) 0)
       42)))
(define-term p₄
  ((def f (λ (n) (if n (set! n 42) 43)))
   (def opq •)
   ((ref f) (ref opq))))
(define-term ex14
  ((def f
     (λ (input)
       (λ (extra)
         (COND
          [(AND (integer? input) (cons? extra) (integer? (car extra)))
           41]
          #:else 42))))
   (def input •)
   (def extra •)
   (((ref f) (ref input)) (ref extra))))

(define/contract (debug p)
  (prog? . -> . (values ξ? (integer? ξ? . -> . ξ?) Cs? σ? Ξ? M? Cs?))
  (match-define (list ds ... e) p)
  (define ξ₀ (term (𝑰/ξ ,e)))
  (define r (→/ξ ds))
  (define (→ξ ξ)
    (car (apply-reduction-relation r ξ)))
  (define (→ n ξ)
    (cond [(zero? n) ξ]
          [else (→ (- n 1) (→ξ ξ))]))
  (match-define (list (list Cs σ Ξ M)) (apply-reduction-relation* r ξ₀ #:cache-all? #t))
  (values ξ₀ → Cs σ Ξ M
          (for/set ([C Cs] #:unless (third C)) C)))

