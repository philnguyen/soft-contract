#lang typed/racket/base
(require
 racket/match racket/set racket/list racket/bool racket/function racket/format
 "utils.rkt" "lang.rkt" "runtime.rkt" "machine.rkt" "reduction.rkt")
(require/typed "parse.rkt"
  [files->prog ((Listof Path-String) → -prog)])

(define-type -tσ Integer)
(define-type -tΞ Integer)
(define-type -t (List -tσ -tΞ))

(define -t₀ : -t (list 0 0))

(define (t>= [t₁ : -t] [t₂ : -t]) : Boolean
  (match-define (list x₁ y₁) t₁)
  (match-define (list x₂ y₂) t₂)
  (and (>= x₁ x₂) (>= y₁ y₂)))

;; configuration
(struct -Cfg ([e : -E] [Γ : -Γ] [κ : -κ]) #:transparent)
;; state with widened stores and summarization
(struct -ξ ([S : (Map -Cfg -t)]
            [F : (Setof -Cfg)]
            [tσ : -tσ] [σ : -σ]
            [tΞ : -tΞ] [Ξ : -Ξ]
            [M : -M]) #:transparent)

(: 𝑰/ξ : -prog → -ξ)
;; Load initial widened state
(define (𝑰/ξ p)
  (match-define (-ς E Γ κ σ Ξ M) (𝑰 p))
  (define C (-Cfg E Γ κ))
  (-ξ (hash C (list 0 0))
      {set C}
      0 σ
      0 Ξ
      M))

(: Cfg-final? : -Cfg -Ξ → Boolean)
(define (Cfg-final? C Ξ)
  (match-define (-Cfg E _ τ) C)
  (final? E τ Ξ))

(: ξ-done? : -ξ → Boolean)
(define (ξ-done? ξ) (set-empty? (-ξ-F ξ)))

(define (show-Cfg [C : -Cfg]) : (Listof Sexp)
  (match-define (-Cfg E Γ κ) C)
  `((E: ,(show-E E))
    (Γ: ,@(show-Γ Γ))
    (κ: ,(show-κ κ))))

(define (show-ξ [ξ : -ξ]) : (Listof Sexp)
  (match-define (-ξ S F _ σ _ Ξ M) ξ)
  `((seen: ,@(for/list : (Listof Sexp) ([(C t) S])
               `(,@(show-Cfg C) ↦ ,@t)))
    (front: ,@(for/list : (Listof Sexp) ([C F]) (show-Cfg C)))
    (σ: ,@(show-σ σ))
    (Ξ: ,@(show-Ξ Ξ))
    (M: ,@(show-M M))))

;;;;; For testing only

(require/typed profile
  [profile-thunk ([(→ Void)] [#:delay Real #:repeat Integer] . ->* . Void)])

(define-syntax-rule (profile* e ...)
  (profile-thunk (λ () e ...) #:delay 0.0001 #:repeat 10)
  ;(begin e ...)
  )

(profile*

  (: ↦/ξ : -ξ → -ξ)
  (define (↦/ξ ξ)
    (match-define (-ξ S F tσ σ tΞ Ξ M) ξ)
    (dbg 'F "|F|: ~a~n" (set-count F))
    ; Compute the intermediate new (narrow states)
    (define I
      (for/fold ([I : (Setof -ς) ∅]) ([C F])
        (match-define (-Cfg E Γ τ) C)
        (match (↦ (-ς E Γ τ σ Ξ M))
          [(? set? s) (∪ I s)]
          [(? -ς? ς) (set-add I ς)])))
    ; Compute the shared widened stores
    (define-values (σ* Ξ* M*)
      (for/fold ([σ* : -σ σ] [Ξ* : -Ξ Ξ] [M* : -M M])
                ([ςi I])
        (match-define (-ς _ _ _ σi Ξi Mi) ςi)
        (values (⊔/m σ* σi) (⊔/m Ξ* Ξi) (⊔/m M* Mi))))
    (define tσ* (if (equal? σ σ*) tσ (+ 1 tσ)))
    (define tΞ* (if (equal? Ξ Ξ*) tΞ (+ 1 tΞ)))
    ; Compute the next frontier and newly seen (narrow) states
    (define-values (F* S*)
      (for/fold ([F* : (Setof -Cfg) ∅] [S* : (Map -Cfg -t) S])
                ([ςi I])
        (match-define (-ς Ei Γi τi _ _ _) ςi)
        (define Ci (-Cfg Ei Γi τi))
        (define ti (hash-ref S* Ci #f))
        (define t* (list tσ* tΞ*))
        (cond [(and ti (t>= ti t*)) (values F* S*)]
              [else (values (set-add F* Ci) (hash-set S* Ci t*))])))
    (-ξ S* F* tσ* σ* tΞ* Ξ* M*))

  (: dbg/ξ : Path-String → (Integer → -ξ))
  (define (dbg/ξ p)

    ;; TODO: can't use `time` in TR...
    (collect-garbage) (collect-garbage) (collect-garbage)
    (define t₁ (current-milliseconds))
    (define evals
      (let go : (Map Integer -ξ)
           ([ξ : -ξ (𝑰/ξ (files->prog (list p)))]
            [evals : (Map Integer -ξ) (hash)]
            [i : Integer 0])
       (define evals* (hash-set evals i ξ))
       (cond
         [(ξ-done? ξ) evals*]
         [else (go (↦/ξ ξ) evals* (+ 1 i))])))
    (define t₂ (current-milliseconds))
    (printf "Time: ~as~n" (~r (exact->inexact (/ (- t₂ t₁) 1000)) #:precision 4))
    
    (define (step [n : Integer]) : -ξ
      (hash-ref evals n (λ () (error 'dbg/ξ "only defined for [0,~a]"
                                     (- (hash-count evals) 1)))))
    
    (define answers
      (let ()
        (match-define (-ξ S* F* _ σ* _ Ξ* M*)
          (hash-ref evals (- (hash-count evals) 1)))
        (printf "States: ~a~n" (hash-count S*))
        (printf "Steps: ~a~n" (hash-count evals))
        (printf "|σ|: ~a~n" (hash-count σ*))
        (printf "|Ξ|: ~a~n" (hash-count Ξ*))
        (printf "|M|: ~a~n" (hash-count M*))))
    
    step)

  (define f
    (parameterize ([debugs {set}])
      (dbg/ξ "test/programs/safe/2.rkt")))
  (define F (compose show-ξ f))
  (void))
