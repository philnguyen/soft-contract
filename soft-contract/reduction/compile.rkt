#lang typed/racket/base

(provide compile@)

(require (for-syntax racket/base
                     racket/syntax
                     syntax/parse)
         (only-in racket/function const)
         racket/set
         racket/list
         racket/match
         typed/racket/unit
         syntax/parse/define
         set-extras
         unreachable
         abstract-compilation
         "../utils/main.rkt"
         "../ast/signatures.rkt"
         "../runtime/signatures.rkt"
         "signatures.rkt"
         )

(define-unit compile@
  (import meta-functions^ static-info^
          env^ val^ sto^ evl^
          kont^ widen^)
  (export compile^)

  (: ↓ₚ : (Listof -module) -e → ⟦E⟧)
  ;; Compile program
  (define (↓ₚ ms E)
    (match ms
      ['() (↓ₑ '† E)]
      [(cons m ms)
       (define ⟦m⟧ (↓ₘ m))
       (define ⟦m⟧s (map ↓ₘ ms))
       (define ⟦E⟧ (↓ₑ '† E))
       (λ (Ρ Φ^ K H Σ) (⟦m⟧ Ρ Φ^ (K:Bgn `(,@⟦m⟧s ,⟦E⟧) Ρ K) H Σ))]))

  (: ↓ₘ : -module → ⟦E⟧)
  ;; Compile module
  (define (↓ₘ m)
    (match-define (-module l ds) m)

    (: ↓pc : -provide-spec → ⟦E⟧)
    (define-compiler ((↓pc spec) Ρ Φ^ K H Σ)
      ;; Wrap contract
      [=> (-p/c-item x C ℓ)
          (⟦C⟧ Ρ Φ^ (K:Dec ℓ 𝒾 K) H Σ)
          #:where
          [𝒾 (-𝒾 x l)]
          [⟦C⟧ (↓ₑ l C)]]
      ;; Export same as internal
      [=> (? symbol? x)
          (begin0 (Ξ K H)
            (assert (defined-at? Σ α))
            (⊔ₐ! Σ K (R↓ A Φ^))
            (⊔ᵥ! Σ α* (Σᵥ@ Σ α)))
       #:where
       [α  (mk-α (-α:top (-𝒾 x l)))]
       [α* (mk-α (-α:wrp (-𝒾 x l)))]
       [A  (list {set -void})]])
    
    (: ↓d : -module-level-form → ⟦E⟧)
    (define-compiler ((↓d d) Ρ Φ^ K H Σ)
      [=> (-define-values xs E)
          (⟦E⟧ Ρ Φ^ (K:Def l αs K) H Σ)
          #:where
          [αs (for/list : (Listof α) ([x (in-list xs)]) (mk-α (-α:top (-𝒾 x l))))]
          [⟦E⟧ (↓ₑ l E)]]
      [(-provide '()) (mk-V -void)]
      [=> (-provide (cons spec specs))
          (⟦spec⟧ Ρ Φ^ (K:Bgn ⟦spec⟧s Ρ K) H Σ)
          #:where
          [⟦spec⟧ (↓pc spec)]
          [⟦spec⟧s (map ↓pc specs)]]
      [(? -e? E) (↓ₑ l E)]
      [_ (begin0 (mk-V -void)
           (log-warning "↓d: ignore ~a~n" d))])

    (match ds
      ['() (mk-V -void)]
      [(cons D Ds)
       (define ⟦D⟧ (↓d D))
       (define ⟦D⟧s (map ↓d Ds))
       (λ (Ρ Φ^ K H Σ)
         (⟦D⟧ Ρ Φ^ (K:Bgn ⟦D⟧s Ρ K) H Σ))]))

  (: ↓ₑ : -l -e → ⟦E⟧)
  (define (↓ₑ l e)
    (: ↓-bnd : (Pairof (Listof Symbol) -e) → (Pairof (Listof Symbol) ⟦E⟧))
    (define (↓-bnd bnd)
      (match-define (cons x eₓ) bnd)
      (cons x (↓ eₓ)))

    (: ↓-dom : -dom → ⟦dom⟧)
    (define ↓-dom
      (match-lambda
        [(-dom xs ?dep e ℓ) (⟦dom⟧ xs ?dep (↓ e) ℓ)]))
    
    (: ↓ : -e → ⟦E⟧)
    (define-compiler ((↓ E) Ρ Φ^ K H Σ)
      [(? -prim? p) (mk-V p)]
      [(-•) (mk-V (-● ∅))]
      [(-x (? symbol? x) ℓₓ) (↓ₓ x ℓₓ)]
      [=> (-λ xs E*)
          (begin0 (Ξ K H)
            (⊔ₐ! Σ K (R↓ (Clo xs ⟦E*⟧ (m↓ Ρ fvs)) Φ^)))
          #:where [fvs (fv E)]
          #:recur E*]
      [=> (-x (and 𝒾 (-𝒾 x lₒ)) _)
          (begin0 (Ξ K H)
            (⊔ᵥ! Σ α (map/set modify-V (Σᵥ@ Σ α))))
          #:where
          [α (mk-α ((if (equal? lₒ l) -α:top -α:wrp) 𝒾))]
          [modify-V
           (ann (cond
                  [(equal? lₒ l) values]
                  [(symbol? l) (λ (V) (with-negative-party l V))]
                  [(λ ([V : V])
                     (with-positive-party 'dummy+
                       (with-negative-party l
                         (match V
                           [(X/G l³ C _) (X/G l³ C α•)]
                           [_ V]))))])
                (V → V))]]
      [=> (-@ E Es ℓ)
          (⟦E⟧ Ρ Φ^ (K:Ap '() ⟦Es⟧ Ρ ℓ K) H Σ)
          #:where ; HACK
          [_ (match* (E Es)
               [('scv:mon (cons (-b (? symbol? l)) _))
                (add-transparent-module! (symbol->string l))
                (add-transparent-module! (format "user-of-~a" l))]
               [(_ _) 'ignore])]
          #:recur E (Es ...)]
      [=> (-if E E₁ E₂)
          (⟦E⟧ Ρ Φ^ (K:If l ⟦E₁⟧ ⟦E₂⟧ Ρ K) H Σ)
          #:recur E E₁ E₂]
      [(-wcm Eₖ Eᵥ E) (error '↓ₑ "TODO: wcm")]
      [(-begin '()) (mk-V -void)]
      [=> (-begin (cons E Es))
          (⟦E⟧ Ρ Φ^ (K:Bgn ⟦Es⟧ Ρ K) H Σ)
          #:recur E (Es ...)]
      [=> (-begin0 E₀ Es)
          (⟦E₀⟧ Ρ Φ^ (K:Bgn0:V ⟦Es⟧ Ρ K) H Σ)
          #:recur E₀ (Es ...)]
      [(-quote (? Base? b)) (mk-V (-b b))]
      [(-quote q) (error '↓ₑ "TODO: (quote ~a)" q)]
      [(-let-values '() E _) (↓ E)]
      [=> (-let-values bnds E ℓ)
          (⟦E⟧ₓ Ρ Φ^ (K:Let ℓ x ⟦bnd⟧s '() ⟦E⟧ Ρ K) H Σ)
          #:where [(cons (cons x ⟦E⟧ₓ) ⟦bnd⟧s) (map ↓-bnd bnds)]
          #:recur E]
      [(-letrec-values '() E _) (↓ E)]
      [=> (-letrec-values bnds E ℓ)
          (let ([Ρ* (init-undefined! Σ bnds H Ρ)])
            (⟦E⟧ₓ Ρ* Φ^ (K:Letrec ℓ x ⟦bnd⟧s ⟦E⟧ Ρ* K) H Σ))
          #:where
          [(cons (cons x ⟦E⟧ₓ) ⟦bnd⟧s) (map ↓-bnd bnds)]
          [init-undefined!
           (λ ([Σ : Σ] [bnd : (Assoc (Listof Symbol) -e)] [H : H] [Ρ₀ : Ρ])
             (for*/fold ([Ρ : Ρ Ρ₀])
                        ([bnd (in-list bnds)] [x (in-list (car bnd))])
               (define α (mk-α (-α:x x H)))
               (⊔ᵥ! Σ α -undefined)
               (Ρ+ Ρ x α)))]
          #:recur E]
      [=> (-set! x E)
          (⟦E⟧ Ρ Φ^ (K:Set! (get-addr Ρ) K) H Σ)
          #:where [get-addr
                   (if (symbol? x)
                       (λ ([Ρ : Ρ]) (Ρ@ Ρ x))
                       (λ _ (mk-α (-α:top x))))]
          #:recur E]
      [(-error msg ℓ)
       (mk-A (Blm/simp ℓ 'Λ '(not-reached) (list (set (-b msg)))))]
      [=> (-μ/c x C)
          (⟦C⟧ (Ρ+ Ρ x (mk-α (-α:x/c x H))) Φ^ (K:Μ/C x K) H Σ)
          #:recur C]
      [(--> Cs D ℓ) (mk--> ℓ (-var-map ↓ Cs) (↓ D))]
      [(-->i Cs D) (mk-->i (map ↓-dom Cs) (↓-dom D))]
      [=> (-∀/c xs E*)
          (begin0 (Ξ K H)
            (⊔ₐ! Σ K (R↓ (∀/C xs ⟦E*⟧ (m↓ Ρ fvs)) Φ^)))
          #:where [fvs (fv E)]
          #:recur E*]
      [=> (-x/c x)
          (begin0 (Ξ K H)
            (⊔ₐ! Σ K (R↓ (X/C (Ρ@ Ρ x)) Φ^)))]
      #;(with-cases-on e (ρ H φ Σ ⟦k⟧)
          [(--> cs d ℓ) #:same-as (mk--> ℓ (-var-map ↓ cs) (↓ d))]
        [(-->i cs d) #:same-as (mk-->i (map (↓dom l) cs) ((↓dom l) d))]
        [(-struct/c 𝒾 cs ℓ)
         #:same-as
         (with-cases-on cs (ρ H φ Σ ⟦k⟧)
           ['()
            (⟦k⟧ (if (struct-defined? Σ φ) C blm) H φ Σ)
            #:where [C (list {set (-St/C #t 𝒾 '())})]]
           [(cons (:↓ ⟦c⟧) (:↓* ⟦c⟧s))
            (if (struct-defined? Σ φ)
                (⟦c⟧ ρ H φ Σ (struct/c∷ ℓ 𝒾 '() ⟦c⟧s ρ ⟦k⟧))
                (⟦k⟧ blm H φ Σ))])
         #:where
         [α (-α->⟪α⟫ 𝒾)]
         [blm (blm/simp l 'Λ '(struct-defined?) (list {set (-𝒾-name 𝒾)}) ℓ)]
         [builtin-struct-tag? (match? 𝒾 (== -𝒾-cons) (== -𝒾-box))]
         [struct-defined?
          (if builtin-struct-tag?
              (λ _ #t)
              (λ ([Σ : -Σ] [φ : -φ]) (defined-at? Σ (-φ-cache φ) α)))]]
        [_ (error '↓ₑ "unhandled: ~a" (show-e e))]
        )
      )
    (↓ e)) 

  (define/memo (↓ₓ [x : Symbol] [ℓₓ : ℓ]) : ⟦E⟧
    ???
    #|
    (define -blm.undefined
      (blm/simp (ℓ-src ℓₓ) 'Λ (list 'defined?) (list {set (format-symbol "~a_(~a)" 'undefined x)}) ℓₓ))
    (remember-e!
     (-x x ℓₓ)
     (λ (ρ H φ Σ ⟦k⟧)
       (for/union : (℘ -ς) ([V-φ (in-list (σ@/cache Σ φ (ρ@ ρ x)))])
          (match-define (cons V^ φ*) V-φ)
          (define (on-ok) (⟦k⟧ {list (set-remove V^ -undefined)} H φ* Σ))
          (define (on-er) (⟦k⟧ -blm.undefined H φ* Σ))
          (if (∋ V^ -undefined)
              (∪ (on-ok) (on-er))
              (on-ok)))))
    |#)

  (define (mk-V [V : V]) (mk-A (list {set V})))

  (define/memo (mk-A [A : A]) : ⟦E⟧
    (λ (Ρ Φ^ K H Σ)
      (begin0 (Ξ K H)
        (⊔ₐ! Σ K (R↓ A Φ^)))))

  (define/memo (mk-->i [⟦dom⟧s : (Listof ⟦dom⟧)] [⟦rng⟧ : ⟦dom⟧]) : ⟦E⟧
    (λ (Ρ Φ^ K H Σ)
      (define-values (Doms doms) (split-⟦dom⟧s Ρ (append ⟦dom⟧s (list ⟦rng⟧))))
      (match doms
        ['() (begin0 (Ξ K H)
               (⊔ₐ! Σ K (R↓ (mk-=>i Σ H Doms) Φ^)))]
        [(cons (⟦dom⟧ x #f ⟦C⟧ ℓ) ⟦dom⟧s)
         (⟦C⟧ Ρ Φ^ (K:==>i Ρ Doms (cons x ℓ) ⟦dom⟧s K) H Σ)])))

  (define/memo (mk--> [ℓ : ℓ] [⟦dom⟧s : (-maybe-var ⟦E⟧)] [⟦rng⟧ : ⟦E⟧]) : ⟦E⟧
    (match ⟦dom⟧s
      ['()
       (λ (Ρ Φ^ K H Σ) (⟦rng⟧ Ρ Φ^ (K:==>:Rng '() #f ℓ K) H Σ))]
      [(cons ⟦C⟧ ⟦C⟧s)
       (λ (Ρ Φ^ K H Σ) (⟦C⟧ Ρ Φ^ (K:==>:Dom '() ⟦C⟧s #f ⟦rng⟧ Ρ ℓ K) H Σ))]
      [(-var ⟦C⟧s ⟦Cᵣ⟧)
       (match ⟦C⟧s
         ['()
          (λ (Ρ Φ^ K H Σ) (⟦Cᵣ⟧ Ρ Φ^ (K:==>:Rst '() ⟦rng⟧ Ρ ℓ K) H Σ))]
         [(cons ⟦C⟧ ⟦C⟧s)
          (λ (Ρ Φ^ K H Σ) (⟦C⟧ Ρ Φ^ (K:==>:Dom '() ⟦C⟧s ⟦Cᵣ⟧ ⟦rng⟧ Ρ ℓ K) H Σ))])]))

  #| 

  (: ↓ₑ : -l -e → -⟦e⟧)
  ;; Compile expression to computation
  (define (↓ₑ l e)
    
    (let ↓ : -⟦e⟧ ([e : -e e])
         (: ↓-bnd : (Pairof (Listof Symbol) -e) → (Pairof (Listof Symbol) -⟦e⟧))
         (define (↓-bnd bnd)
           (match-define (cons x eₓ) bnd)
           (cons x (↓ eₓ))) 
         
      )) 

   

  (define/memo (mk-let* [ℓ : ℓ]
                        [⟦bind⟧s : (Listof (Pairof Symbol -⟦e⟧))]
                        [⟦body⟧ : -⟦e⟧]) : -⟦e⟧
    (foldr
     (λ ([⟦bind⟧ : (Pairof Symbol -⟦e⟧)] [⟦body⟧ : -⟦e⟧]) : -⟦e⟧
       (match-define (cons (app list x) ⟦e⟧ₓ) ⟦bind⟧)
       (λ (ρ H φ Σ ⟦k⟧)
         (⟦e⟧ₓ ρ H φ Σ (let∷ ℓ x '() '() ⟦body⟧ ρ ⟦k⟧))))
     ⟦body⟧
     ⟦bind⟧s)) 

  (define/memo (mk-mon [ctx : -ctx] [⟦c⟧ : -⟦e⟧] [⟦e⟧ : -⟦e⟧]) : -⟦e⟧
    (λ (ρ H φ Σ ⟦k⟧)
      (⟦c⟧ ρ H φ Σ (mon.v∷ ctx (cons ⟦e⟧ ρ) ⟦k⟧))))

  (define/memo (mk-app [ℓ : ℓ] [⟦f⟧ : -⟦e⟧] [⟦x⟧s : (Listof -⟦e⟧)]) : -⟦e⟧
    (remember-e!
     (-@ (recall/show ⟦f⟧) (map recall/show ⟦x⟧s) ℓ) 
     (λ (ρ H φ Σ ⟦k⟧)
      (⟦f⟧ ρ H φ Σ (ap∷ '() ⟦x⟧s ρ ℓ ⟦k⟧))))) 

  (define/memo (mk-fc [l : -l] [ℓ : ℓ] [⟦c⟧ : -⟦e⟧] [⟦v⟧ : -⟦e⟧]) : -⟦e⟧
    (λ (ρ H φ Σ ⟦k⟧)
      (⟦c⟧ ρ H φ Σ (fc.v∷ l ℓ ⟦v⟧ ρ ⟦k⟧))))

  (define/memo (mk-wrapped-hash [C : -Hash/C] [ctx : -ctx] [α : ⟪α⟫] [V : -V^]) : -⟦e⟧
    (λ (ρ H φ Σ ⟦k⟧)
      (⟦k⟧ (list {set (-Hash/guard C α ctx)}) H (alloc Σ φ α V) Σ)))

  (define/memo (mk-wrapped-set [C : -Set/C] [ctx : -ctx] [α : ⟪α⟫] [V : -V^]) : -⟦e⟧
    (λ (ρ H φ Σ ⟦k⟧)
      (⟦k⟧ (list {set (-Set/guard C α ctx)}) H (alloc Σ φ α V) Σ))) 

  (define-syntax-parser with-cases-on
    [(_ e:expr (ρ:id H:id φ:id Σ:id ⟦k⟧:id) clauses ...)
     (define parse-clause
       (syntax-parser
         [[e-pat #:same-as expr
                 (~optional (~seq #:where [x d] ...)
                            #:defaults ([(x 1) null]
                                        [(d 1) null]))]
          #`[e-pat
             (match-define x d) ...
             expr]]
         [[e-pat rhs
                 (~optional (~seq #:where [x d] ...)
                            #:defaults ([(x 1) null]
                                        [(d 1) null]))]
          #'[e-pat
             (match-define x d) ...
             (λ (ρ H φ Σ ⟦k⟧) rhs)]]))
     #`(match e #,@(map parse-clause (syntax->list #'(clauses ...))))])
  |#

  (: split-⟦dom⟧s : Ρ (Listof ⟦dom⟧) → (Values (Listof Dom) (Listof ⟦dom⟧)))
  (define (split-⟦dom⟧s Ρ ⟦dom⟧s)
    (let go ([Doms↓ : (Listof Dom) '()] [⟦dom⟧s : (Listof ⟦dom⟧) ⟦dom⟧s])
      (match ⟦dom⟧s
        ['() (values Doms↓ '())]
        [(cons (⟦dom⟧ x ?dep ⟦E⟧ ℓ) ⟦dom⟧s*)
         (match ?dep
           [(? values) (go (cons (Dom x (Clo ?dep ⟦E⟧ Ρ) ℓ) Doms↓) ⟦dom⟧s*)]
           [#f (values Doms↓ ⟦dom⟧s)])])))
  )
