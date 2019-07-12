#lang typed/racket/base

(provide termination@)

(require typed/racket/unit
         racket/match
         racket/set
         set-extras
         unreachable
         "../runtime/signatures.rkt"
         "../ast/signatures.rkt"
         "signatures.rkt"
         )

(define-unit termination@
  (import static-info^
          prover^)
  (export termination^)

  (: update-M : Σ M CP CP W → (Option M))
  (define (update-M Σ M er ee W)
    (define G (make-sc-graph Σ (binders er) W))
    ;; Quirk: only fail if target is a lambda.
    ;; In particular, ignore any loop from a wrapped function to itself.
    (cond
      ;; Immediate graph fails sc, fail
      [(and (-λ? ee) (equal? er ee) (sc-violating? G)) #f]
      [else
       (define ΔM (transitive-graphs M er ee G))
       (and (not (and (-λ? ee) (set-ormap sc-violating? (hash-ref ΔM ee mk-∅))))
            (merge-M (merge-M M ee (hash er {set G})) ee ΔM))]))

  (define binders : (CP → (Listof Symbol))
    (match-lambda
      [(-λ (-var xs _) _ _) xs]
      [(? list? xs) xs]))

  (: transitive-graphs : M CP CP SCG → (Immutable-HashTable CP (℘ SCG)))
  (define (transitive-graphs M₀ src tgt G)
    (for/hash : (Immutable-HashTable CP (℘ SCG))
        ([(src₀ Gs₀) (in-hash (hash-ref M₀ src (inst hash CP (℘ SCG))))])
      (values src₀ ((inst map/set SCG SCG) (λ ([G₀ : SCG]) (concat-graph G₀ G)) Gs₀))))

  (: sc-violating? : SCG → Boolean)
  (define (sc-violating? G)
    (and (equal? G (concat-graph G G))
         (not (for/or : Boolean ([(edge ch) (in-hash G)])
                (and (eq? ch '↓)
                     (eq? (car edge) (cdr edge)))))))

  (: merge-M : M CP (Immutable-HashTable CP (℘ SCG)) → M)
  (define (merge-M M₀ tgt tbl)
    ((inst hash-update CP (Immutable-HashTable CP (℘ SCG)))
     M₀ tgt
     (λ (tbl₀)
       (for/fold ([tbl* : (Immutable-HashTable CP (℘ SCG)) tbl₀])
                 ([(src Gs) (in-hash tbl)])
         (hash-update tbl* src (λ ([Gs₀ : (℘ SCG)]) (∪ Gs₀ Gs)) mk-∅)))
     hash))

  (: has-sc-violation? : M → Boolean)
  (define (has-sc-violation? M)
    (for/or : Boolean ([(tgt M*) (in-hash M)])
      (set-ormap sc-violating? (hash-ref M* tgt mk-∅))))

  (: make-sc-graph : Σ (Listof Symbol) W → SCG)
  (define (make-sc-graph Σ xs W)
    (define Σ* (with-dummy xs W Σ))
    (for*/hash : SCG ([(x i₀) (in-indexed xs)]
                      [(D₁ i₁) (in-indexed W)]
                      [?↓ (in-value (cmp Σ* (γ:lex x) D₁))]
                      #:when ?↓)
      (values (cons i₀ i₁) ?↓)))

  (: with-dummy : (Listof Symbol) W Σ → Σ)
  (define (with-dummy xs W Σ)
    (define ● {set (-● ∅)})
    (cons (car Σ)
          (let ([Γ₁ (for*/fold ([Γ : Γ (cdr Σ)]) ([x (in-list xs)]
                                                  [γ (in-value (γ:lex x))]
                                                  #:unless (hash-has-key? Γ γ))
                      (hash-set Γ γ ●))])
            (for*/fold ([Γ : Γ Γ₁]) ([V (in-list W)]
                                     #:when (T? V)
                                     #:unless (hash-has-key? Γ V)
                                     #:unless (and (T:@? V) (-st-ac? (T:@-_0 V))))
              (hash-set Γ V ●)))))

  (: concat-graph : SCG SCG → SCG)
  (define (concat-graph G₁ G₂)
    (for*/fold ([G* : SCG (hash)])
               ([(edge₁ ch₁) (in-hash G₁)]
                [i (in-value (cdr edge₁))]
                [(edge₂ ch₂) (in-hash G₂)] #:when (eq? i (car edge₂)))
      (hash-update G* (cons (car edge₁) (cdr edge₂))
                   (λ ([ch₀ : Ch]) (Ch-best ch₀ ch₁ ch₂))
                   (λ () '↧))))

  (define Ch-best : (Ch * → Ch)
    (match-lambda*
      [(list '↧ ...) '↧]
      [_ '↓]))

  (: cmp : Σ γ D → (Option Ch))
  (define (cmp Σ T₀ D₁)
    (: must-be? : D¹ P → Boolean)
    (define (must-be? V P) (eq? '✓ (sat Σ P (D¹->D V))))
    (: must-be?₂ : D¹ P D¹ → Boolean)
    (define (must-be?₂ V₁ P V₂) (eq? '✓ (sat Σ P (D¹->D V₁) (D¹->D V₂))))

    (: ≺? : D¹ T → Boolean)
    ;; Check for definite "smaller-ness". `#f` means "don't know"
    (define (≺? V₀ T)
      (or (V₀ . sub-value? . T)
          (and (V₀ . must-be? . 'integer?)
               (T  . must-be? . 'integer?)
               (or (and (-zero . must-be?₂ . '<= V₀)
                        (V₀ . must-be?₂ . '< T))
                   (and (V₀ . must-be?₂ . '<= -zero)
                        (T  . must-be?₂ . '< V₀))))))

    (cond [(equal? '✓ (sat Σ 'equal? T₀ D₁)) '↧]
          [(if (set? D₁)
               (for/and : Boolean ([V₁ (in-set D₁)])
                 (≺? V₁ T₀))
               (≺? D₁ T₀))
           '↓]
          [else #f]))

  (: sub-value? : D¹ T → Boolean)
  (define (T₁ . sub-value? . T₂)
    (match T₁
      [(T:@ (? sub-ac?) (list T*))
       (let loop ([T : (U T -prim) T*])
         (match T
           [(== T₂) #t]
           [(T:@ (? sub-ac?) (list T*)) (loop T*)]
           [_ #f]))]
      [_ #f]))

  (: sub-ac? : K → Boolean)
  ;; Check for function whose result is guaranteed smaller than argument
  (define (sub-ac? K)
    (case K
      [(caar cdar cadr cddr
        caaar caadr cadar caddr cdaar cdadr cddar cdddr
        caaaar caaadr caadar caaddr cadaar cadadr caddar cadddr
        cdaaar cdaadr cdadar cdaddr cddaar cddadr cdddar cddddr)
       #t]
      [else
       (match K
         [(-st-ac 𝒾 i) (not (struct-mutable? 𝒾 i))] ; TODO make sure right for substructs
         [_ #f])]))

  (define (D¹->D [x : D¹]) (if (or (T? x) (-prim? x)) x {set x}))
  )
