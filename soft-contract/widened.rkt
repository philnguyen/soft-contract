#lang typed/racket/base
(require
 racket/match racket/set racket/list racket/bool racket/function racket/format
 "utils.rkt" "lang.rkt" "runtime.rkt" "machine.rkt" "reduction.rkt")
(require/typed "parse.rkt"
  [files->prog ((Listof Path-String) → -prog)])

(define-type -tσ Integer)
(define-type -tΞ Integer)
(define-type -tM Integer)

(struct -tς ([E : -E] [Γ : -Γ] [τ : -τ] [tσ : -tσ] [tΞ : -tΞ] [tM : -tM]) #:transparent)

(define (show-tς [ς : -tς]) : (Listof Sexp)
  (match-define (-tς E Γ τ σ Ξ M) ς)
  `((E: ,(show-E E))
    (Γ: ,@(show-Γ Γ))
    (τ: ,(show-τ τ))
    (σ: ,σ)
    (Ξ: ,Ξ)
    (M: ,M)))

;; configuration
(struct -Cfg ([e : -E] [Γ : -Γ] [τ : -τ]) #:transparent)
;; state with widened stores and summarization
(struct -ξ ([S : (Setof -tς)] [F : (Setof -Cfg)]
            [tσ : -tσ] [σ : -σ] [σs : (Listof -σ)]
            [tΞ : -tΞ] [Ξ : -Ξ] [Ξs : (Listof -Ξ)]
            [tM : -tM] [M : -M] [Ms : (Listof -M)]) #:transparent)

(: 𝑰/ξ : -prog → -ξ)
;; Load initial widened state
(define (𝑰/ξ p)
  (match-define (and ς (-ς E Γ τ σ Ξ M)) (𝑰 p))
  (-ξ {set (-tς E Γ τ 0 0 0)} {set (-Cfg E Γ τ)}
      0 σ (list σ)
      0 Ξ (list Ξ)
      0 M (list M)))

(: Cfg-final? : -Cfg -Ξ → Boolean)
(define (Cfg-final? C Ξ)
  (match-define (-Cfg E _ τ) C)
  (final? E τ Ξ))

(: ξ-done? : -ξ → Boolean)
(define (ξ-done? ξ) (set-empty? (-ξ-F ξ)))

(define (show-Cfg [C : -Cfg]) : (Listof Sexp)
  (match-define (-Cfg E Γ τ) C)
  `((E: ,(show-E E))
    (Γ: ,@(show-Γ Γ))
    (τ: ,(show-τ τ))))

(define (show-ξ [ξ : -ξ]) : (Listof Sexp)
  (match-define (-ξ S F _ σ _ _ Ξ _ _ M _) ξ)
  `((seen: ,@(for/list : (Listof Sexp) ([ς S]) (show-tς ς)))
    (front: ,@(for/list : (Listof Sexp) ([C F]) (show-Cfg C)))
    (σ: ,@(show-σ σ))
    (Ξ: ,@(show-Ξ Ξ))
    (M: ,@(show-M M))))

;;;;; For testing only
(begin

  (: ↦/ξ : -ξ → -ξ)
  (define (↦/ξ ξ)
    (match-define (-ξ S F tσ σ σs tΞ Ξ Ξs tM M Ms) ξ)
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
    (define-values (tσ* σs*)
      (cond [(equal? σ σ*) (values tσ σs)]
            [else (values (+ 1 tσ) (cons σ* σs))]))
    (define-values (tΞ* Ξs*)
      (cond [(equal? Ξ Ξ*) (values tΞ Ξs)]
            [else (values (+ 1 tΞ) (cons Ξ* Ξs))]))
    (define-values (tM* Ms*)
      (cond [(equal? M M*) (values tM Ms)]
            [else (values (+ 1 tM) (cons M* Ms))]))
    ; Compute the next frontier and newly seen (narrow) states
    (define-values (F* S*)
      (for/fold ([F* : (Setof -Cfg) ∅] [S* : (Setof -tς) ∅])
                ([ςi I])
        (match-define (-ς Ei Γi τi _ _ _) ςi)
        (define ς* (-tς Ei Γi τi tσ* tΞ* tM*))
        (cond [(∋ S ς*) (values F* S*)]
              [else (values (set-add F* (-Cfg Ei Γi τi))
                            (set-add S* ς*))])))
    (-ξ (∪ S S*) F* tσ* σ* σs* tΞ* Ξ* Ξs* tM* M* Ms*))

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
        (match-define (-ξ S* F* _ σ* _ _ Ξ* _ _ M* _)
          (hash-ref evals (- (hash-count evals) 1)))
        (printf "States: ~a~n" (set-count S*))
        (printf "Steps: ~a~n" (hash-count evals))
        (printf "|σ|: ~a~n" (hash-count σ*))
        (printf "|Ξ|: ~a~n" (hash-count Ξ*))
        (printf "|M|: ~a~n" (hash-count M*))))
    
    step)

  (define f
    (parameterize ([debugs {set}])
      (dbg/ξ "test/programs/safe/1.rkt")))
  (define F (compose show-ξ f))
  )
