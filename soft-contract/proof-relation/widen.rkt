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

  (: V⊕ : -σ -φ -V^ -V^ → -V^)
  (define (V⊕ σ φ V₁ V₂)
    (define-values (Vs δV)
      (if (>= (set-count V₁) (set-count V₂))
          (values V₁ V₂)
          (values V₂ V₁)))
    (for/fold ([V^ : -V^ Vs]) ([Vᵢ (in-set δV)])
      (V^⊕ σ φ V^ Vᵢ)))

  (: V^⊕ : -σ -φ -V^ -V → -V^)
  (define (V^⊕ σ φ V^ V)
    (cond
      [(∋ V^ V) V^]
      [(for/or : (Option (Pairof (℘ -h) -V)) ([V₀ (in-set V^)])
         (match (compat? σ φ V₀ V)
           [(? set? ps) (cons ps V₀)]
           [_ #f]))
       =>
       (match-lambda
         [(cons ps V₀) (set-add (set-remove V^ V₀) (-● ps))])]
      [else (set-add V^ V)]))

  (: compat? : -σ -φ -V -V → (Option (℘ -h)))
  (define (compat? σ φ V₁ V₂)
    (match* (V₁ V₂)
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
     [((and V₁ (? -●?)) (and V₂ (? -b?))) (compat? σ φ V₂ V₁)]
     [((-● ps₁) (-● ps₂))
      (define ps (ps⊕ ps₁ ps₂))
      (and (not (set-empty? ps)) ps)]
     [((? -t? t₁) (? -t? t₂))
      #:when (and (not (-b? t₁)) (not (-b? t₂)) (not (equal? t₁ t₂)))
      (define ps₁ (hash-ref (-φ-condition φ) t₁ mk-∅))
      (define ps₂ (hash-ref (-φ-condition φ) t₂ mk-∅))
      (if (and (set-empty? ps₁) (set-empty? ps₂)) ∅ (ps⊕ ps₁ ps₂))]
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

