#lang typed/racket/base

(provide prover@)

(require (for-syntax racket/base
                     racket/syntax
                     syntax/parse)
         racket/match
         (except-in racket/set for/set for*/set for/seteq for*/seteq)
         racket/list
         racket/bool
         racket/vector
         typed/racket/unit
         syntax/parse/define
         set-extras
         unreachable
         typed-racket-hacks
         "../utils/main.rkt"
         "../ast/signatures.rkt"
         "../runtime/signatures.rkt"
         "../signatures.rkt"
         "signatures.rkt"

         "sat-result.rkt"
         "local-prover-core.rkt"
         "ext-prover-core.rkt")

(define-unit prover-core@
  (import static-info^
          val^ evl^ sto^
          sat-result^ (prefix l: local-prover-core^) (prefix x: ext-prover-core^))
  (export prover^)
  (init-depend local-prover-core^)

  (: split-results ([Σ (U R R^)] [T #:fast? Boolean] . ->* . (Values R^ R^)))
  (define (split-results Σ R₀ [P 'values] #:fast? [fast? #f])
    (define-values (R✓ R✗ R?) (partition-results Σ R₀ P #:fast? fast?))
    (define (refine+ [R : R]) (l:∧  R P))
    (define (refine- [R : R]) (l:∧¬ R P))
    (for/fold ([R✓* : R^ (map/set refine+ R✓)]
               [R✗* : R^ (map/set refine- R✗)])
              ([R (in-set R?)])
      (values (set-add R✓* (refine+ R))
              (set-add R✗* (refine- R)))))

  (: partition-results ([Σ (U R R^)] [T #:fast? Boolean] . ->* . (Values R^ R^ R^)))
  (define (partition-results Σ R₀ [P 'values] #:fast? [fast? #f])
    (: go : R → (Values R^ R^ R^))
    (define (go R)
      (define-values (R✓ R✗ R?) (with-checker l:check Σ P R))
      (assert (<= (set-count R?) 1)) ; TODO just for debugging
      (if (and (not fast?) (not (set-empty? R?)))
          (let-values ([(R✓* R✗* R?*) (with-checker x:check Σ P (set-first R?))])
            ;; TODO: unneccesary spliting of `R✓*` and `R✗*` here. Collapse!
            (values (∪ R✓ R✓*) (∪ R✗ R✗*) R?*))
          (values R✓ R✗ R?)))
    (if (R? R₀)
        (go R₀)
        (for/collect ∪ [∅ : R^] (R✓ R✗ R?) ([Rᵢ (in-set R₀)]) (go Rᵢ))))

  (: check-one-of : Φ^ T^ (Listof Base) → ?Dec)
  (define (check-one-of Φ^ T^ bs)
    (cond [(set? T^) (⊔*/set (λ ([V : V]) (l:check-one-of V bs)) T^)]
          [(V? T^) (l:check-one-of T^ bs)]
          [else #f]))

  (define T-arity l:T-arity)
  (define T->V l:T->V)

  (: R->V : (U Σ Σᵥ) (U R R^) → V^)
  (define (R->V Σ R*)
    (define go : (R → V^) (match-lambda [(R (list T) Φ^) (T->V Σ Φ^ T)]))
    (if (set? R*) (set-union-map go R*) (go R*)))

  (define V^+ l:V^+)
  (define Ψ+ l:Ψ+)
  (define Ps⊢P l:Ps⊢P)
  (define Ps+ l:Ps+)

  ;; TODO optimize
  (:* defntly? possbly? : ([Σ (U R R^)] [T #:fast? Boolean] . ->* . Boolean))
  (define (defntly? Σ R [P 'values] #:fast? [fast? #f])
    (define-values (R✓ R✗ R?) (partition-results Σ R P #:fast? fast?))
    (and (set-empty? R✗) (set-empty? R?)))
  (define (possbly? Σ R [P 'values] #:fast? [fast? #f])
    (define-values (R✓ R✗ R?) (partition-results Σ R P #:fast? fast?))
    (not (and (set-empty? R✓) (set-empty? R?))))
  
  (: with-checker : (Σ Φ T (Listof T) → ?Dec) Σ T R → (Values R^ R^ R^))
  (define (with-checker check Σ P R₀)
    (match-define (R W₀ Φ^₀) R₀)
    (define n (length W₀))
    (define ✓-Ts : (Vectorof T^) (make-vector n ∅))
    (define ✗-Ts : (Vectorof T^) (make-vector n ∅))
    (define ?-Ts : (Vectorof T^) (make-vector n ∅))
    (define-set ✓-Φ^ : Φ)
    (define-set ✗-Φ^ : Φ)
    (define-set ?-Φ^ : Φ)

    (define ?S : (Integer → (Option S))
      (let ([poses ((inst make-vector (Option S)) n #f)])
        (for ([T (in-list W₀)] [i (in-naturals)] #:unless (set? T))
          (vector-set! poses i T))
        (λ (i) (vector-ref poses i))))

    (define-syntax-rule (W⊔! Ts Ts*)
      (for ([Tᵢ (in-list Ts*)] [i (in-naturals)])
        (define Tᵢ*
          (match (?S i)
            [(? values S) S]
            [_ (set-add (assert (vector-ref Ts i) set?) (assert Tᵢ V?))]))
        (vector-set! Ts i Tᵢ*)))

    (: check-with! : (Listof T) → Void)
    (define (check-with! Ts)
      (for ([Φ (in-set Φ^₀)])
        (case (check Σ Φ P Ts)
          [(✓)  (W⊔! ✓-Ts Ts) (✓-Φ^-add! Φ)]
          [(✗)  (W⊔! ✗-Ts Ts) (✗-Φ^-add! Φ)]
          [else (W⊔! ?-Ts Ts) (?-Φ^-add! Φ)])))

    (: collect : (Vectorof T^) Φ^ → R^)
    (define (collect W Φ^)
      (cond [(or (set-empty? Φ^) (vector-member ∅ W)) ∅]
            [else {set (R (vector->list W) Φ^)}]))
    
    (let go! ([W : W W₀] [acc : (Listof T) '()])
      (match W
        ['() (check-with! (reverse acc))]
        [(cons T^ W*)
         (if (set? T^)
             (for ([V (in-set T^)]) (go! W* (cons V acc)))
             (go! W* (cons T^ acc)))]))
    
    (values (collect ✓-Ts ✓-Φ^) (collect ✗-Ts ✗-Φ^) (collect ?-Ts ?-Φ^)))

  (define-syntax for/collect
    (syntax-parser
      [(for/collect ⊕ (v₀ (~literal :) T) (x ...) (for-clauses ...) body ...)
       (with-syntax ([(z ...) (for/list ([x (syntax->list #'(x ...))])
                                (format-id x "~a*" x))])
         #'(for/fold ([x : T v₀] ...) (for-clauses ...)
             (define-values (z ...) (let () body ...))
             (values (⊕ x z) ...)))]))
  )

(define-compound-unit/infer prover@
  (import static-info^ meta-functions^ sto^ val^ evl^ prims^)
  (export prover^)
  (link sat-result@ local-prover-core@ ext-prover-core@ prover-core@))

#|
(define-unit pre-proof-system@
  (import static-info^ sat-result^ path^ pretty-print^
          (prefix local: local-prover^)
          (prefix ext: external-prover^))
  (export proof-system^)
  (init-depend local-prover^ external-prover^)

  

  (: V- : -σ -φ -V^ (U -h -V) → -V^)
  (define (V- σ φ V^ C)
    (define V₁- : (-V (U -h -V) → -V)
      (match-lambda**
       [((-● ps) (? -h? h)) (-● (∪ (set-remove ps h)
                                   (if (-prim? h) {set (-not/c h)} ∅)))]
       [(V _) V]))
    (for/fold ([acc : -V^ V^])
              ([V (in-set V^)])
      (case (V∈C σ φ {set V} C)
        [(✓) (set-remove acc V)]
        [(✗) acc]
        [(?) (set-add (set-remove acc V) (V₁- V C))])))
  )
|#
