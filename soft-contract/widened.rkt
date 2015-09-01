#lang typed/racket/base
(require
 racket/match racket/set racket/list racket/bool racket/function
 "utils.rkt" "lang.rkt" "runtime.rkt" "machine.rkt" "reduction.rkt")
(require/typed "parse.rkt"
  [files->prog ((Listof Path-String) → -prog)])

;; configuration
(struct -Cfg ([e : -E] [Γ : -Γ] [τ : -τ]) #:transparent)
;; state with widened stores and summarization
(struct -ξ ([cs : (Setof -Cfg)] [σ : -σ] [Ξ : -Ξ] [M : -M]) #:transparent)

(: 𝑰/ξ : -prog → -ξ)
;; Load initial widened state
(define (𝑰/ξ p)
  (match-define (-ς E Γ τ σ Ξ M) (𝑰 p))
  (-ξ {set (-Cfg E Γ τ)} σ Ξ M))

(: Cfg-final? : -Cfg -Ξ → Boolean)
(define (Cfg-final? C Ξ)
  (match-define (-Cfg E _ τ) C)
  (final? E τ Ξ))

(: ↦/ξ : -ξ → (Option -ξ))
;; Reduction relation on widened state
(define (↦/ξ ξ)
  ;; FIXME: do this the efficient way
  (match-define (-ξ Cs σ Ξ M) ξ)
  (define ςs
    (for/fold ([ςs : (Setof -ς) ∅])
              ([C Cs] #:unless (Cfg-final? C Ξ))
      (match-define (-Cfg E Γ τ) C)
      (match (↦ (-ς E Γ τ σ Ξ M))
        [(? -ς? ς) (set-add ςs ς)]
        [(? set? s) (set-union ςs s)])))
  (define-values (Cs* σ* Ξ* M*)
    (for/fold ([Cs* : (Setof -Cfg) Cs] [σ* : -σ σ] [Ξ* : -Ξ Ξ] [M* : -M M])
              ([ςi ςs])
      (match-define (-ς Ei Γi τi σi Ξi Mi) ςi)
      (values (set-add Cs* (-Cfg Ei Γi τi))
              (⊔/m σ* σi)
              (⊔/m Ξ* Ξi)
              (⊔/m M* Mi))))
  (cond
    [(and (equal? Cs* Cs) (equal? σ* σ) (equal? Ξ* Ξ) (equal? M* M)) #f]
    [else (-ξ Cs* σ* Ξ* M*)]))


;;;;; For testing only
(begin

  (: alloc-int (∀ (X) (→ (X → Integer))))
  (define (alloc-int)
    (let ([m : (Map X Integer) (make-hash)])
      (λ ([x : X]) : Integer
         (hash-ref! m x (λ () (hash-count m))))))

  (define alloc-τ ((inst alloc-int -τ)))
  (define alloc-α ((inst alloc-int -α)))

  (: show-ξ : -ξ → Sexp)
  (define (show-ξ ξ)
    (match-define (-ξ Cs σ Ξ M) ξ)

    (define (show-α [α : -α]) : Symbol
      (string->symbol (format "α~a" (n-sub (alloc-α α)))))
    
    (define show-σ
      (for/list : (Listof Sexp) ([(α Vs) (in-hash σ)])
        `(,(show-α α) ↦ ,@(for/list : (Listof Sexp) ([V Vs]) (show-V V)))))

    (define (show-τ [τ : -τ]) : Symbol
      (string->symbol (format "τ~a" (n-sub (alloc-τ τ)))))

    (define (show-ρ [ρ : -ρ]) : (Listof Sexp)
      (for/list ([(x α) (in-hash ρ)])
        `(,x ↦ ,(show-α α))))

    (define (show-E [E : -E]) : Sexp
      (match E
        [(-↓ e ρ) `(,(show-e e) ,(show-ρ ρ))]
        [(-W Vs e) `(,@(map show-V Vs) @ ,(and e (show-e e)))]
        [(-blm l+ lo C V) `(blame ,l+ ,lo ,(show-V C) ,(map show-V V))]
        [_ '♣]))

    (define show-φ : (-φ → Sexp)
      (match-lambda
        [(-φ.if t e) `(if ,(show-E t) ,(show-E e))]
        [(? -φ.let-values?) `let-values…]
        [(? -φ.letrec-values?) `letrec-values…]
        [(? -φ.set!?) `set!…]
        [(-φ.@ Es Ws _)
         `(,@(reverse (map show-V (map (inst -W-x -V) Ws)))
           □ ,@(map show-E Es))]
        [(-φ.begin es _) `(begin ,@(map show-e es))]
        [(-φ.begin0v es _) `(begin0 □ ,@(map show-e es))]
        [(-φ.begin0e (-W Vs _) es _)
         `(begin0 ,(map show-V Vs) ,@(map show-e es))]
        [(-φ.rt.@ Γ xs f args)
         `(rt ,(show-Γ Γ) (,(and f (show-e f))
                           ,@(for/list : (Listof Sexp) ([x xs] [arg args])
                               `(,x ↦ ,(and arg (show-e arg))))))]
        [(-φ.rt.let dom) `(rt/let ,@(set->list dom))]
        [(-φ.=>i cs Cs↓ cs↓ xs e ρ)
         `(=>i ,@(reverse (map show-V Cs↓)) □ ,@(map show-e cs))]
        [(-φ.indy.dom x xs cs Cs args args↓ V_f d ρ l³)
         `(indy-args ,x
                     ,(reverse (map (inst car Symbol -WV) args↓))
                     ,(for/list : (Listof Sexp) ([x xs] [C Cs])
                        `(,x ▹ ,(show-V C)))
                     ,(show-V V_f))]
        [(-φ.indy.rng V_f args l³)
         `(indy-rng ,(show-V V_f)
                    ,(for/list : (Listof Sexp) ([arg args])
                       (match-define (-W V e) arg)
                       `(,(show-V V) @ ,(and e (show-e e)))))]
        [_ 'φ•]))

    (define (show-κ [κ : -κ]) : Sexp
      (match-define (-κ φ τ) κ)
      `(κ: ,(show-φ φ) ,(show-τ τ)))

    (define show-Ξ
      (for/list : (Listof Sexp) ([(τ κs) (in-hash Ξ)])
        `(,(show-τ τ) ↦ ,@(for/list : (Listof Sexp) ([κ κs]) (show-κ κ)))))
    
    `(,(for/list : (Listof Sexp) ([C Cs])
         (match-define (-Cfg E Γ τ) C)
         `(Cfg ,(show-E E) ,(show-Γ Γ) ,(show-τ τ)))
      ,show-σ
      ,show-Ξ))
  
  (: ξ-subtract : -ξ -ξ → -ξ)
  ;; Compute new stuff in `ξ₁` not in `ξ₀`
  (define (ξ-subtract ξ₁ ξ₀)
    (match-define (-ξ Cs₀ σ₀ Ξ₀ M₀) ξ₀)
    (match-define (-ξ Cs₁ σ₁ Ξ₁ M₁) ξ₁)
    (-ξ (set-subtract Cs₁ Cs₀)
        (mmap-subtract σ₁ σ₀)
        (mmap-subtract Ξ₁ Ξ₀)
        (mmap-subtract M₁ M₀)))

  (: dbg/ξ : Path-String → (Values (Integer → -ξ) (Integer → -ξ) (Setof -Cfg)))
  (define (dbg/ξ p)
    (define ξ₀ (𝑰/ξ (files->prog (list p))))
    
    (define-values (ξ evals)
      (let go : (Values -ξ (Map Integer -ξ))
           ([ξ ξ₀] [i 1] [evals : (Map Integer -ξ) (hash 0 ξ₀)])
        (define ξ* (↦/ξ ξ))
        (cond
          [ξ* (go ξ* (+ i 1) (hash-set evals i ξ*))]
          [else (values ξ evals)])))
    
    (define (step [n : Integer]) : -ξ
      (hash-ref evals n (λ () (error 'dbg/ξ "only defined for [~a,~a]"
                                     0 (- (hash-count evals) 1)))))
    
    (define (diff [n : Integer]) : -ξ
      (ξ-subtract (step n) (step (- n 1))))

    (define answers
      (let ()
        (match-define (-ξ Cs* _ Ξ* _) (hash-ref evals (- (hash-count evals) 1)))

        (for*/set: : (Setof -Cfg) ([C Cs*] #:when (Cfg-final? C Ξ*))
          C)))
    
    (values step diff answers))

  (define-values (f d ans) (dbg/ξ "test/programs/safe/1.rkt"))
  (define F (compose show-ξ f))
  (define (D [n : Integer]) (show-ξ (d n)))
  )
