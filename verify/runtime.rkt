#lang typed/racket/base
(require racket/match racket/set racket/list
         "../utils.rkt" "../lang.rkt" "../runtime.rkt")
(require/typed redex/reduction-semantics [variable-not-in (Any Sym → Sym)])
(provide (all-defined-out)
         (except-out (all-from-out "../runtime.rkt") .Case .Case@ .Case+ Case∅))

(: subst/L : (case→ [.L .F → .L]
                    [.// .F → .//]
                    [.μ/V .F → .μ/V]
                    [(U .// .μ/V) .F → (U .// .μ/V)]
                    [.V .F → .V]
                    [.U .F → .U]
                    [(Listof .V) .F → (Listof .V)]
                    [(Setof .V) .F → (Setof .V)]))
(define (subst/L V F)
  (: go : (case→ [.L → .L] [.// → .//] [.μ/V → .μ/V] [(U .// .μ/V) → (U .// .μ/V)]
                 [.V → .V] [.U → .U] [.ρ → .ρ]
                 [(Listof .V) → (Listof .V)] [(Setof .V) → (Setof .V)]))
  (define go
    (match-lambda
      ; V
      [(and V (.L i)) (match (hash-ref F i #f)
                        [(? int? j) (.L j)]
                        [#f V])]
      [(.// U C*) (.// (go U) (for/set: .V ([Ci C*]) (go Ci)))]
      [(.μ/V x V*) (.μ/V x (for/set: .V ([Vi V*]) (go Vi)))]
      [(? .X/V? V) V]
      ; U
      [(.Ar C V l) (.Ar (go C) (go V) l)]
      [(.St t V*) (.St t (go V*))]
      [(.λ↓ f ρ) (.λ↓ f (go ρ))]
      [(.Λ/C Cx (.↓ e ρ) v?) (.Λ/C (go Cx) (.↓ e (go ρ)) v?)]
      [(.St/C t V*) (.St/C t (go V*))]
      [(.μ/C x C) (.μ/C x (go C))]
      [(and U (or (? .X/C?) (? .prim?) (? .•?))) U]
      ; ρ
      [(.ρ m l)
       (.ρ
        (for/fold: : (Map (U Sym Int) .V) ([acc : (Map (U Sym Int) .V) m]) ([k (in-hash-keys m)])
          (match (hash-ref m k #f)
            [#f acc]
            [(? .V? V) (hash-set acc k (go V))]))
        l)]
      ; List
      [(? list? V*) (map go V*)]
      [(? set? s) (for/set: .V ([V s]) (go V))]))
  (go V))

(: transfer : .σ .V .σ .F → (List .σ .V .F))
; transfers value from old heap to new heap, given mapping F
(define (transfer σ-old V-old σ-new F)
  (: go! : (case→ [.L → .L]
                 [(U .// .μ/V) → (U .// .μ/V)]
                 [.V → .V]
                 [.U → .U]
                 [(Listof .V) → (Listof .V)]
                 [.ρ → .ρ]))
  (define (go! V-old)
    (match V-old
      ; V
      [(.L i) (match (hash-ref F i #f)
                [(? int? j) (.L j)]
                [#f
                 (match-define-values (σ′ (and L_j (.L j))) (σ+ σ-new))
                 (set! σ-new σ′)
                 (set! F (hash-set F i j))
                 (let ([V′ (go! (σ@ σ-old i))])
                   (set! σ-new (σ-set σ-new j V′))
                   L_j)])]
      [(.// U C*)
       #;(printf "Looking at ~a~n~n" C*)
       (.// (go! U) (for/set: .V ([Ci C*] #:when (transfer? Ci))
                                 #;(printf "Transferring ~a~n~n" Ci) (go! Ci)))]
      [(.μ/V x V*) (.μ/V x (for/set: .V ([Vi V*]) (go! Vi)))]
      [(? .X/V? V) V]
      ; U
      [(.Ar C V l) (.Ar (go! C) (go! V) l)]
      [(.St t V*) (.St t (go! V*))]
      [(.λ↓ f ρ) (.λ↓ f (go! ρ))]
      [(.Λ/C Cx (.↓ e ρ) v?) (.Λ/C (go! Cx) (.↓ e (go! ρ)) v?)]
      [(.St/C t V*) (.St/C t (go! V*))]
      [(.μ/C x C) (.μ/C x (go! C))]
      [(and U (or (? .X/C?) (? .prim?) (? .•?))) U]
      ;ρ
      [(.ρ m l)
       (.ρ
        (for/fold : (Map (U Sym Int) .V) ([acc : (Map (U Sym Int) .V) m]) ([k (in-hash-keys m)])
          (match (hash-ref m k #f)
            [#f acc]
            [(? .V? V) (hash-set acc k (go! V))]))
        l)]
      ; List
      [(? list? V*) (map go! V*)]))
  
  (: transfer? : .V → Bool)
  (define (transfer? C)
    (match C
      [(.L i) (hash-has-key? F i)]
      [(.// U _) (match U
                   [(? .prim?) #t]
                   [(.•) #f]
                   [(.Ar C V _) (and (transfer? C) (transfer? V))]
                   [(.St _ V*) (andmap transfer? V*)]
                   [(.λ↓ f (.ρ m _)) (for/and : Bool ([V (in-hash-values m)])
                                       (transfer? V))]
                   [(.Λ/C C (.ρ m _) _)
                    (and (andmap transfer? C)
                         (for/and : Bool ([V (in-hash-values m)])
                           (transfer? V)))]
                   [(.St/C _ C*) (andmap transfer? C*)]
                   [(.μ/C _ c) (transfer? c)]
                   [(? .X/C?) #t])]
      [_ #f]))
  
  (: well-formed? : .σ .V → Boolean)
  (define (well-formed? σ V)
    (match V
      [(.// U C*)
       (and (for/and : Boolean ([C C*]) (well-formed? σ C))
            (match U
              [(.St _ V*) (for/and : Boolean ([Vi V*]) (well-formed? σ Vi))]
              [(.λ↓ _ (.ρ m _))
               (for/and : Boolean ([i (in-hash-keys m)])
                 (well-formed? σ (hash-ref m i)))]
              [_ #t]))]
      [(.L i) (and (hash-has-key? (.σ-map σ) i)
                   (well-formed? σ (σ@ σ i)))]
      [_ #t]))
  
  (let ([V-new (go! V-old)])
    #;(unless (well-formed? σ-new V-new)
      (error "malformed"))
    (list σ-new V-new F)))

(: V-abs : (case→ [.σ .L → (U .// .μ/V)]
                  [.σ .// → .//]
                  [.σ .μ/V → .μ/V]
                  [.σ (U .// .μ/V) → (U .// .μ/V)]
                  [.σ .X/V → .X/V]
                  [.σ .V → (U .// .μ/V .X/V)]
                  [.σ .λ↓ → .λ↓]
                  [.σ .U → .U]
                  [.σ (Listof .V) → (Listof .V)]
                  [.σ .ρ → .ρ]))
(define (V-abs σ V*)
  (: go : (case→ [.L → (U .// .μ/V)]
                 [.// → .//]
                 [.μ/V → .μ/V]
                 [(U .// .μ/V) → (U .// .μ/V)]
                 [.X/V → .X/V]
                 [.V → (U .// .μ/V .X/V)]
                 [.λ↓ → .λ↓]
                 [.U → .U]
                 [(Listof .V) → (Listof .V)]
                 [.ρ → .ρ]))
  (define go
    (match-lambda
      [(.L i) (go (σ@ σ i))]
      [(.// U C*)
       (.// (go U)
            (for/set: .V ([C C*]
                          ;#:unless ; discard dynamically generated refinements
                          #;(match? C (.// (.λ↓ (.λ 1 (.@ (.=) (list (.x 0) _) 'Λ) #f) _) _)))
              C))]
      ; FIXME: ok to ignore other forms??
      [(? .μ/V? V) V]
      [(? .X/V? V) V]
      [(? .U? U) (match U
                   [(.Ar C V′ l^3) (.Ar (go C) (go V′) l^3)]
                   [(.St t V*′) (.St t (map go V*′))]
                   [(.λ↓ f ρ) (.λ↓ f (go ρ))]
                   [_ U])]
      [(? list? V*) (map go V*)]
      [(.ρ m l) (.ρ (for/fold ([m′ m]) ([(i V) (in-hash m)])
                      (hash-set m′ i (go V))) l)]))
  (go V*))

;; checks whether v appears under V
(: V∈ : .V .V → Bool)
(define (V∈ v V)
  (let go ([V V])
    (or (equal? v V) ; TODO: Not enough for sat-7
        (match V
          [(.// (.St _ V*) _) (ormap go V*)]
          [(.// (.Ar _ V′ _) _) (go V′)]
          [(.μ/V _ V*) (for/or ([V V*]) (go V))]
          [_ #f]))))

(: unroll : .μ/V → (Setof .V))
(define (unroll V)
  (match-let ([(.μ/V x V*) V]) (V/ V* (.X/V x) V)))

(: V/ : (case→ [.V .V .V → .V]
               [(Listof .V) .V .V → (Listof .V)]
               [(Setof .V) .V .V → (Setof .V)]
               [.ρ .V .V → .ρ]))
(define (V/ V0 V1 Vn)
  (: go : (case→ [.V → .V] [.ρ → .ρ]))
  (define go
    (match-lambda
      [(? .V? V)
       (if (equal? V V1) Vn
           (match V
             [(.// U1 C*)
              (.// (match U1
                     [(.Ar C V l^3) (.Ar C (go V) l^3)]
                     [(.St t V*) (.St t (map go V*))]
                     [(.λ↓ f ρ) (.λ↓ f (go ρ))]
                     [_ U1]) ; TODO ok to ignore other forms?
                   C*)]
             [(.μ/V z Vs) (match V1
                            [(.X/V x) (if (eq? x z) V (.μ/V z (for/set: .V ([V Vs]) (go V))))]
                            [_ (.μ/V z (for/set: .V ([V Vs]) (go V)))])]
             [x x]))]
      [(and ρ (.ρ m l))
       (let ([m′ (for/fold ([m′ : (Map (U Int Sym) .V) m∅]) ([x (in-hash-keys m)])
                   (hash-set m′ x (go (hash-ref m x))))])
         (if (equal? m′ m) ρ (.ρ m′ l)))]))
  (match V0
    [(? set? s) (for/set: .V ([x s]) (go x))]
    [(? list? l) (map go l)]
    [(? .V? V) (go V)]
    [(? .ρ? ρ) (go ρ)]))

; generates a symbol not appearing in value (for μ/V x {...})
(: fresh : (U .V (Setof .V) (Listof .V)) → Sym)
(define (fresh V)
  
  (: col : (U .V (Setof .V) (Listof .V)) → (Setof Sym))
  (define (col V)
    (match V
      [(.L _) ∅]
      [(.// U C*)
       (match U
         [(.Ar _ V _) (col V)]
         [(.St _ Vs) (col Vs)]
         [_ ∅])] ; TODO ok to ignore?
      [(.μ/V x Vs) (col Vs)]
      [(.X/V x) {set x}]
      [(? set? V*) (for/fold ([s : (Setof Sym) ∅]) ([V V*])
                     (set-union s (col V)))]
      [(? list? V*) (for/fold ([s : (Setof Sym) ∅]) ([V V*])
                      (set-union s (col V)))]))
  
  (variable-not-in (set->list (col V)) 'X))
