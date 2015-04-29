#lang typed/racket/base
(require racket/match racket/function racket/set
         "../utils.rkt" "../lang.rkt" "../runtime.rkt" "../provability.rkt"
         (prefix-in raw: "../delta.rkt"))
(provide δ refine refine1)

(: δ : .σ .o (Listof .V) Mon-Party → .Ans*)
(define (δ σ o V* l)
  (parameterize ([raw:refine1 refine1])
    (raw:δ σ o V* l)))

(: refine : .σ .V (U (Setof .V) (Listof .V) .V) * → (Values .σ .V))
(define (refine σ V . Css)
  (parameterize ([raw:refine1 refine1])
    (apply raw:refine σ V Css)))

(: refine1 : .σ .V .V → (Values .σ .V))
(define (refine1 σ V C)
  (parameterize ([raw:refine1 refine1])
    (let ([C (simplify C)])
      
      (when (match? C (.// '• _)) (error "ha!"))
      (match V
        [(.L i)
         (define-values (σ* V*) (refine1 σ (σ@ σ i) C))
         (match V*
           [(.// (.St t Vs) Cs)
            (define-values (σ** Vs*) (raw:alloc* σ* Vs))
            (define V** (.// (.St t Vs*) Cs))
            (values (σ-set σ** i V**) V)]
           [(? .//? V′) (values (σ-set σ* i V*) V)]
           [_ (error "broken =_=" V)])]
        [(.// U C*)
         (match C
           [(.L _) (values σ (.// U (set-add C* C)))]
           [(.// Uc _)          
            (match Uc
              [(.St (.id 'and/c 'Λ) (list C1 C2)) (raw:refine σ V C1 C2)]
              [(.St (.id 'or/c 'Λ) (list C1 C2))
               #;(begin
               (define ¬mt (.¬/C (Prim 'empty?)))
               (define ¬cons (.¬/C (Prim 'cons?)))
               (when (equal? C1 (Prim 'empty?))))
              (match* ((⊢ σ V C1) (⊢ σ V C2))
                [('X 'X) (error "WTF??")]
                [(_ 'X) (refine1 σ V C1)]
                [('X _) (refine1 σ V C2)]
                [(_ _) (refine-U σ U (raw:refine-C* C* C))])]
            [(? .μ/C? Uc) (refine1 σ V (unroll/C Uc))]
            ; equal contracts
            [(.λ↓ (.λ 1 (.@ (or '= 'equal?) (list (.x 0) e) _)) ρ)
             (match e
               [(? .b? b) (values σ (.// b C*))]
               [(and (? .λ? f) (? closed?)) (values σ (.// (.λ↓ f ρ∅) C*))]
               [(.x i) (match (ρ@ ρ (- i 1))
                         [(.L a) (match-let ([(.// U′ C*′) (σ@ σ a)])
                                   (values σ (.// (raw:U+ U U′) (raw:∪* C* C*′ C))))]
                         [(.// U′ C*′) (values σ (.// (raw:U+ U U′) (raw:∪* C* C*′)))])]
               [_ (refine-U σ U (raw:refine-C* C* C))])]
            ; struct contracts
            [(.St/C t Ds)
             (define-values (σ₁ Vs₁)
               (match U
                 ['• (σ++ σ (length Ds))]
                 [(.St _ Vs) (values σ Vs)]))
             (define-values (σ₂ Vs₂)
               (raw:refine* σ₁ Vs₁ Ds))
             (values σ₂ (.// (.St t Vs₂) C*))]
            [(.st-p t n)
             (match U
               ['•
                (define-values (σ′ L*) (σ++ σ n)) 
                (values σ′ (.// (.St t L*) C*))]
               [(.St (? (curry equal? t)) _) (values σ V)])]
            ; singleton contracts
            ['true? (values σ (.// .tt C*))]
            ['false? (values σ (.// .ff C*))]
            [(.st-p t 0) (values σ (.// (.St t '()) C*))]
            [_ (refine-U σ U (raw:refine-C* C* C))])])]))))

(: refine-U : .σ .U (Setof .V) → (Values .σ .V))
(define (refine-U σ U Cs)
  (define-values (D/st Ds)
    (set-partition (λ ([C : .V]) (match? C (.// (? .St/C?) _))) Cs))
  (if (set-empty? D/st)
      (values σ (.// U Ds))
      (refine1 σ (.// U Ds) (set-first D/st))))
