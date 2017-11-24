#lang typed/racket/base

(provide widening@)

(require (for-syntax racket/base
                     racket/list
                     racket/syntax
                     syntax/parse)
         racket/match
         racket/list
         racket/set
         racket/bool
         typed/racket/unit
         set-extras
         "../utils/main.rkt"
         "../ast/signatures.rkt"
         "../runtime/signatures.rkt"
         "../signatures.rkt"
         "signatures.rkt")

(define-unit widening@
  (import proof-system^ sto^ path^)
  (export widening^)

  (: V⊕ : -V^ -V^ → -V^)
  (define (V⊕ V₁ V₂)
    (define-values (Vs δV)
      (if (>= (set-count V₁) (set-count V₂))
          (values V₁ V₂)
          (values V₂ V₁)))
    (for/fold ([V^ : -V^ Vs]) ([Vᵢ (in-set δV)])
      (V^⊕ V^ Vᵢ)))

  (: V^⊕ : -V^ -V → -V^)
  (define (V^⊕ V^ V)
    (cond
      [(∋ V^ V) V^]
      [(for/or : (Option (Pairof (℘ -h) -V)) ([V₀ (in-set V^)])
         (match (compat? V₀ V)
           [(? set? ps) (cons ps V₀)]
           [_ #f]))
       =>
       (match-lambda
         [(cons ps V₀) (set-add (set-remove V^ V₀) (-● ps))])]
      [else (set-add V^ V)]))

  (: compat? : -V -V → (Option (℘ -h)))
  (define compat?
    (match-lambda**
     [((-b b₁) (-b b₂))
      #:when (not (equal? b₁ b₂))
      (define-syntax-rule (best-predicate p? ...)
        (cond [(and (p? b₁) (p? b₂)) {set 'p?}] ...
              [else #f]))
      (best-predicate
       exact-positive-integer? exact-nonnegative-integer? exact-integer?
       integer? real? number?
       path-string? string?
       char? boolean?
       regexp? pregexp? byte-regexp? byte-pregexp?)]
     [((? -b? b) (-● ps))
      (define ps*
        (for/set: : (℘ -h) ([p (in-set ps)] #:when (equal? '✓ (p∋V^ ⊥σ φ₀ p {set b})))
          p))
      (and (not (set-empty? ps)) ps*)]
     [((and V₁ (? -●?)) (and V₂ (? -b?))) (compat? V₂ V₁)]
     [((-● ps₁) (-● ps₂))
      (define ps (ps⊕ ps₁ ps₂))
      (and (not (set-empty? ps)) ps)]
     [(_ _) #f]))

  (: ps⊕ : (℘ -h) (℘ -h) → (℘ -h))
  (define (ps⊕ ps₁ ps₂)
    (for*/union : (℘ -h) ([p₁ (in-set ps₁)] [p₂ (in-set ps₂)]) (p⊕ p₁ p₂)))

  (: p⊕ : -h -h → (℘ -h))
  (define (p⊕ p q)
    (cond [(equal? '✓ (p⇒p q p)) {set p}]
          [(equal? '✓ (p⇒p p q)) {set q}]
          [else ∅]))

  )

