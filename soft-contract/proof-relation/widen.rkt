#lang typed/racket/base

(provide σ⊕! σ⊕*! V+)

(require racket/match
         racket/set
         "../utils/main.rkt"
         "../ast/definition.rkt"
         "../runtime/main.rkt"
         "local.rkt")

(: σr⊔ : -σ -σr -V Boolean → -σr)
(define (σr⊔ σ σr V bind?)
  (match-define (-σr Vs bind?₀) σr)
  (-σr (Vs⊕ σ Vs V) (and bind?₀ bind?)))

(: σ⊕! : -σ -α -V Boolean → Void)
(define (σ⊕! σ α V bind?)
  (match-define (-σ m i) σ)
  (match-define (and σr (-σr Vs b?)) (hash-ref m α (λ () ⊥σr)))
  (unless (and (∋ Vs V) (equal? b? bind?))
    (set--σ-m! σ (hash-update m α (λ ([σr : -σr]) (σr⊔ σ σr V bind?)) (λ () ⊥σr)))
    (set--σ-version! σ (assert (+ 1 i) fixnum?))))

(define-syntax σ⊕*!
  (syntax-rules (↦)
    [(_ σ [α ↦ V b?]) (σ⊕! σ α V b?)]
    [(_ σ [α ↦ V b?] p ...)
     (begin
       (σ⊕!  σ α V b?)
       (σ⊕*! σ p ...))]))

(: V⊑ : -σ -V -V → Boolean)
;; Check if `V₂` definitely subsumes `V₁`
;; `#f` is a conservative "don't know" answer
(define (V⊑ σ V₁ V₂)
  (let loop ([V₁ : -V V₁] [V₂ : -V V₂])
    (match* (V₁ V₂)
      [(V V) #t]
      [(_ (-● ps)) #:when (not (behavioral? σ V₁))
       (for/and : Boolean ([p ps])
         (equal? '✓ (p∋Vs σ p V₁)))]
      [(_ _) #f])))

(: Vs⊕ : -σ (℘ -V) -V → (℘ -V))
;; Widen value set with new value
(define (Vs⊕ σ Vs V)
  (: iter : (℘ -V) -V → (U (℘ -V) (Pairof (℘ -V) -V)))
  (define (iter Vs V)
    (match (for/or : (Option (List -V -V -V)) ([Vᵢ Vs])
             (cond [(V⊕ σ Vᵢ V) => (λ ([V* : -V]) (list V* Vᵢ V))]
                   [else #f]))
      [(list V* V₁ V₂)
       (cons (set-remove (set-remove Vs V₁) V₂)
             V*)]
      [#f (set-add Vs V)]))

  (repeat-compact Vs V iter))

(: V+ : -σ -V (U -v -V (℘ -v) (℘ -V)) → -V)
;; Refine opaque value with predicate
(define (V+ σ V P) : -V
  
  (define (simplify [P : -V]) : -V
    (match P
      [(-Ar _ (and α (or (? -α.def?) (? -α.wrp?) (? -e?))) _)
       (define-values (Vs _) (σ@ σ α))
       (cond [(= 1 (set-count Vs)) (simplify (set-first Vs))]
             [else P])]
      [_ P]))
  
  (cond
    [(set? P)
     (for/fold ([V : -V V]) ([Pᵢ (in-set P)])
       (V+ σ V Pᵢ))]
    [else
     (with-debugging/off
       ((V*)
        (match V
          [(-● ps)
           (match P
             [(-λ (list x) (-@ (or '= 'equal? 'eq?)
                               (or (list (-x x) (? -V? V*))
                                   (list (? -V? V*) (-x x)))
                               _))
              #:when V*
              V*]
             ['not -ff]
             ['null? -null]
             ['void? -void]
             [(? -v? v) (-● (ps+ ps v))]
             [(? -V? P)
              (match (simplify P)
                [(? -o? o) (-● (ps+ ps o))]
                [_ V])])]
          [_ V]))
       
       (hash-ref! printing (list V P)
                  (λ ()
                    (printf "~a + ~a -> ~a~n"
                            (show-V V)
                            (if (-v? P) (show-e P) (show-V P))
                            (show-V V*)))))]))

(: ps+ : (℘ -v) -v → (℘ -v))
;; Strengthen refinement set with new predicate
(define (ps+ ps p)
  (define-values (obsoletes p-useless?)
    (for/fold ([obsoletes : (℘ -v) ∅] [p-useless? : Boolean #f])
              ([pᵢ ps])
      (case (p⇒p pᵢ p)
        [(✓) (values obsoletes #t)]
        [(✗) (error "spurious refinement: ~a conflicts with ~a" pᵢ p)]
        [(?)
         (case (p⇒p p pᵢ)
           [(✓) (values (set-add obsoletes pᵢ) p-useless?)]
           [(✗) (error "spurious refinement: ~a conflicts with ~a" pᵢ p)]
           [(?) (values obsoletes p-useless?)])])))
  (cond
    [p-useless? ps]
    [else (set-add (set-subtract ps obsoletes) p)]))

(: V⊕ : -σ -V -V → (Option -V))
;; Widen 2 values to one approximating both.
;; Return `#f` if no approximation preferred
(define (V⊕ σ V₁ V₂)
  (cond
    [(V⊑ σ V₁ V₂) V₂]
    [(V⊑ σ V₂ V₁) V₁]
    [else ;; TODO more heuristics
     (match* (V₁ V₂)
       [((-b 0) (-● ps))
        (define p
          (for/or : (Option -v) ([p ps])
            (match p
              [(-λ (list x) (-@ '< (list (-b 0) (-x x)) _))
               p]
              [(-λ (list x) (-@ '< (list (-x x) (-b 0)) _))
               p]
              [_ #f])))
        (and p (-● (set-remove ps p)))]
       [(_ _) #f])]))

(: repeat-compact (∀ (X) (℘ X) X ((℘ X) X → (U (℘ X) (Pairof (℘ X) X))) → (℘ X)))
(define (repeat-compact xs x f)
  (let loop ([xs : (℘ X) xs] [x : X x])
    (match (f xs x)
      [(cons xs* x*) (loop xs* x*)]
      [(? set? s) s])))
