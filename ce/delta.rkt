#lang typed/racket/base
(require racket/match racket/function racket/set
         "../utils.rkt" "../lang.rkt" "../runtime.rkt" "../provability.rkt"
         (prefix-in raw: "../delta.rkt"))
(provide δ refine)

(: δ : .σ .o (Listof .V) Mon-Party → .Ans*)
(define (δ σ o V* l)
  (parameterize ([raw:refine1 refine1])
    (raw:δ σ o V* l)))

(: refine : .σ .V (U (Setof .V) (Listof .V) .V) * → .Vns)
(define (refine σ V . Css)
  (parameterize ([raw:refine1 refine1])
    (apply raw:refine σ V Css)))

(: refine1 : .σ .V .V → .Vns)
(define (refine1 σ V C)
  (let ([C (simplify C)])
     
    (when (match? C (.// '• _)) (error "ha!"))
    (match V
      [(.L i) (match-let ([(cons σ′ V′) (refine1 σ (σ@ σ i) C)])
                (match V′
                  [(.// (.St t V*) C*) (match-let* ([(cons σ′ V*′) (raw:alloc σ′ V*)]
                                                    [V′ (.// (.St t V*′) C*)])
                                         (cons (σ-set σ′ i V′) V))]
                  [(? .//? V′) (cons (σ-set σ′ i V′) V)]
                  [_ (error "broken =_=" V)]))]
      [(.// U C*)
       (match C
         [(.L _) (cons σ (.// U (set-add C* C)))]
         [(.// Uc _)          
          (match Uc
            [(.St 'and/c (list C1 C2)) (raw:refine σ V C1 C2)]
            [(.St 'or/c (list C1 C2))
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
               [(? .b? b) (cons σ (.// b C*))]
               [(and (? .λ? f) (? closed?)) (cons σ (.// (.λ↓ f ρ∅) C*))]
               [(.x i) (match (ρ@ ρ (- i 1))
                         [(.L a) (match-let ([(.// U′ C*′) (σ@ σ a)])
                                   (cons σ (.// (raw:U+ U U′) (raw:∪ C* C*′ C))))]
                         [(.// U′ C*′) (cons σ (.// (raw:U+ U U′) (raw:∪ C* C*′)))])]
               [_ (refine-U σ U (raw:refine-C* C* C))])]
            ; struct contracts
            [(.St/C t D*)
             (match-let*-values ([(σ V*)
                                  (match U
                                    ['• (σ++ σ (length D*))]
                                    [(.St _ V*) (values σ V*)])]
                                 [((cons σ V*)) (raw:refine* σ V* D*)])
                                (cons σ (.// (.St t V*) C*)))]
            [(.st-p t n)
             (match U
               ['•
                (let-values ([(σ′ L*) (σ++ σ n)])
                  (cons σ′ (.// (.St t L*) C*)))]
               [(.St (? (curry eq? t)) _) (cons σ V)])]
            ; singleton contracts
            ['true? (cons σ (.// .tt C*))]
            ['false? (cons σ (.// .ff C*))]
            [(.st-p t 0) (cons σ (.// (.St t '()) C*))]
            [_ (refine-U σ U (raw:refine-C* C* C))])])])))

(: refine-U : .σ .U (Setof .V) → .Vns)
(define (refine-U σ U Cs)
  (define-values (D/st Ds)
    (set-partition (λ ([C : .V]) (match? C (.// (? .St/C?) _))) Cs))
  (if (set-empty? D/st)
      (cons σ (.// U Ds))
      (refine1 σ (.// U Ds) (set-first D/st))))
