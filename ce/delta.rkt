#lang typed/racket/base
(require racket/match racket/list racket/set racket/function racket/bool
         "../utils.rkt" "../lang.rkt" "../runtime.rkt" "../provability.rkt" "../show.rkt")
(provide (all-defined-out))

(define-syntax-rule (match/Ans* v [p e ...] ...) (match/nd: (.Ans → .Ans) v [p e ...] ...))
(define-syntax-rule (match/Vns* v [p e ...] ...) (match/nd: (.Vns → .Vns) v [p e ...] ...))

(: δ : .σ .o (Listof .V) Symbol → .Ans*)
(define (δ σ o V* l)
  (when (match? o (.st-mk 'box _) (.st-ac 'box _ _) (.st-p 'box _))
    (error "δ does not handle box opreation"))
  #;(printf "δ: o: ~a~nV*: ~a~n~nσ: ~a~n~n~n" o (map (curry show-E σ) V*) (show-σ σ))
  (match* (o V*)
    
    ; primitive predicates
    [((? .pred? o) (list V)) (check-C σ V (→V o))]
    
    ; accessors
    [((.st-ac t _ i) (list (.// (.St t V*) _))) (cons σ (list-ref V* i))]
    [((.st-ac t n i) (list V))
     (match/Ans* (δ σ (.st-p t n) V* 'Λ)
       [(cons σt (.// (.b #t) _)) (match-let ([(.// (.St _ V*) _) (σ@ σt V)])
                                    (cons σt (list-ref V* i)))]
       [(cons σf (.// (.b #f) _)) (cons σf (.blm l (name o) V (→V (.st-p t n))))])]
    
    ; arithmetics
    [('= (list V1 V2))
     (match/Ans* (δ σ 'number? (list V1) 'Λ)
       [(cons σt (.// (.b #t) _))
        (match/Ans* (δ σt 'number? (list V2) 'Λ)
          [(cons σt (.// (.b #t) _)) (Δ σt '= V*)]
          [(cons σf (.// (.b #f) _)) (cons σf (.blm l '= V2 NUM/C))])]
       [(cons σf (.// (.b #f) _)) (cons σf (.blm l '= V1 NUM/C))])]
    [((or 'add1 'sub1) (list V))
     (match/Ans* (δ σ 'number? V* 'Λ)
       [(cons σt (.// (.b #t) _)) (Δ σt o V*)]
       [(cons σf (.// (.b #f) _)) (cons σf (.blm l (name o) V NUM/C))])]
    [((or '+ '- '*) (list V1 V2))
     (match/Ans* (δ σ 'number? (list V1) 'Λ)
       [(cons σt (.// (.b #t) _))
        (match/Ans* (δ σt 'number? (list V2) 'Λ)
          [(cons σt (.// (.b #t) _)) (Δ σt o V*)]
          [(cons σf (.// (.b #f) _)) (cons σf (.blm l (name o) V2 NUM/C))])]
       [(cons σf (.// (.b #f) _)) (cons σf (.blm l (name o) V1 NUM/C))])]
    [('+ (list)) (cons σ (Prim 0))]
    [('* (list)) (cons σ (Prim 1))]
    [((or '+ '*) (list V))
     (match/Ans* (δ σ 'number? (list V) 'Λ)
       [(cons σt (.// (.b #t) _)) (cons σt V)]
       [(cons σf (.// (.b #f) _)) (cons σf V)])]
    [((or '+ '*) (list* V₁ V₂ Vᵣ))
     (match/Ans* (δ σ o (list V₁ V₂) l)
       [(cons σ (? .V? Vᵢ)) (δ σ o (cons Vᵢ Vᵣ) l)]
       [(and ans (cons σ (? .blm?))) ans])]
    [('/ (list V1 V2))
     (match/Ans* (δ σ 'number? (list V1) 'Λ)
       [(cons σt (.// (.b #t) _))
        (match/Ans* (δ σt 'number? (list V2) 'Λ)
          [(cons σt (.// (.b #t) _))
           (match/Ans* (δ σt '= (list V2 (Prim 0)) 'Λ)
             [(cons σt (.// (.b #t) _)) (cons σt (.blm l '/ V2 NON-ZERO/C))]
             [(cons σf (.// (.b #f) _)) (Δ σf '/ V*)])]
          [(cons σf (.// (.b #f) _)) (cons σf (.blm l '/ V2 NUM/C))])]
       [(cons σf (.// (.b #f) _)) (cons σf (.blm l '/ V1 NUM/C))])]
    [((or '> '< '<= '>=) (list V1 V2))
     (match/Ans* (δ σ 'real? (list V1) 'Λ)
       [(cons σt (.// (.b #t) _))
        (match/Ans* (δ σt 'real? (list V2) 'Λ)
          [(cons σt (.// (.b #t) _)) (Δ σt o V*)]
          [(cons σf (.// (.b #f) _)) (cons σf (.blm l (name o) V2 REAL/C))])]
       [(cons σf (.// (.b #f) _)) (cons σf (.blm l (name o) V1 REAL/C))])]
    [('string-length (list V))
     (match/Ans* (δ σ 'string? V* 'Λ)
       [(cons σt (.// (.b #t) _)) (Δ σt 'string-length V*)]
       [(cons σf (.// (.b #f) _)) (cons σf (.blm l 'str-len V STR/C))])]
    [('equal? (list V1 V2)) (V=? σ V1 V2)]
    [('sqrt (list V))
     (match/Ans* (δ σ 'real? (list V) 'Λ)
       [(cons σt (.// (.b #t) _)) (Δ σt 'sqrt V*)]
       [(cons σf (.// (.b #f) _)) (cons σf (.blm l 'sqrt V REAL/C))])]
    
    ; arity check
    [((or 'arity=? 'arity>=? 'arity-includes?) (list V1 V2))
     (match/Ans* (δ σ 'procedure? (list V1) 'Λ)
       [(cons σt (.// (.b #t) _))
        (match/Ans* (δ σt 'integer? (list V2) 'Λ)
          [(cons σt (.// (.b #t) _)) (check-C σt V1 (→C o #:2nd V2))]
          [(cons σf (.// (.b #f) _)) (cons σf (.blm l (name o) V2 INT/C))])]
       [(cons σf (.// (.b #f) _)) (cons σf (.blm l (name o) V1 PROC/C))])]
    ; constructor
    [((.st-mk t n) _)
     (if (= (length V*) n) (cons σ (→V (.St t V*))) (cons σ (.blm l t (Prim (length V*)) (arity=/C n))))]
    ; anything else is error
    [(_ _) (cons σ (.blm l (name o) ♦ (arity=/C -1 #|HACK|#)))]))

(: Δ : .σ .o (Listof .V) → .Vns*)
(define (Δ σ o V*)
  (match* (o V*)
    [('add1 (list V)) (Δ σ '+ (list V ONE))]
    [('sub1 (list V)) (Δ σ '- (list V ONE))]
    
    [('* (list V1 V2))
     (match (for/list: : (Listof .V) ([Vi V*]) (σ@ σ Vi))
       [(list (.// (.b (? number? x)) _) (.// (.b (? number? y)) _)) (cons σ (Prim (* x y)))]
       [(list (and W1 (.// U1 _)) (and W2 (.// U2 _)))
        (let ([X1 (if (.•? U1) V1 W1)]
              [X2 (if (.•? U2) V2 W2)])
          (cond
            [(eq? 'Proved (⊢ σ X1 ZERO/C)) (cons σ ZERO)]
            [(eq? 'Proved (⊢ σ X2 ZERO/C)) (cons σ ZERO)]
            [(eq? 'Proved (⊢ σ X1 ONE/C)) (cons σ X2)]
            [(eq? 'Proved (⊢ σ X2 ONE/C)) (cons σ X1)]
            [else
             (let-values ([(σ L)
                           (σ+ σ
                               (cond [(all-prove? σ V* INT/C) INT/C]
                                     [(all-prove? σ V* REAL/C) REAL/C]
                                     [else NUM/C])
                               (cond [(all-prove? σ V* POS/C) POS/C]
                                     [(all-prove? σ V* NON-NEG/C) NON-NEG/C]
                                     [(all-prove? σ V* NON-ZERO/C) NON-ZERO/C]
                                     [else #f])
                               (*/C X1 X2))])
               (cons σ L))]))])]
    [('/ (list V1 V2))
     (match (for/list: : (Listof .V) ([Vi V*]) (σ@ σ Vi))
       [(list (.// (.b (? number? x)) _) (.// (.b (? number? y)) _)) (cons σ (Prim (/ x y)))]
       [(list (and W1 (.// U1 _)) (and W2 (.// U2 _)))
        (let ([X1 (if (.•? U1) V1 W1)]
              [X2 (if (.•? U2) V2 W2)])
          (cond
            [(eq? 'Proved (⊢ σ X1 ZERO/C)) (cons σ ZERO)]
            [else
             (let-values ([([σ : .σ] [L : .L])
                           (σ+ σ
                               (cond [(all-prove? σ V* REAL/C) REAL/C]
                                     [else NUM/C])
                               (cond [(all-prove? σ V* POS/C) POS/C]
                                     [(all-prove? σ V* NON-NEG/C) NON-NEG/C]
                                     [(eq? 'Proved (⊢ σ V1 NON-ZERO/C)) NON-ZERO/C]
                                     [else #f])
                               (÷/C X1 X2)
                               (if (eq? 'Proved (⊢ σ X1 NON-ZERO/C)) NON-ZERO/C #f))])
               (cons σ L))]))])]
    [('+ (list V1 V2))
     (match (for/list: : (Listof .V) ([Vi V*]) (σ@ σ Vi))
       [(list (.// (.b (? number? x)) _) (.// (.b (? number? y)) _)) (cons σ (Prim (+ x y)))]
       [(list (and W1 (.// U1 _)) (and W2 (.// U2 _)))
        (let ([X1 (if (.•? U1) V1 W1)]
              [X2 (if (.•? U2) V2 W2)])
          (cond
            [(eq? 'Proved (⊢ σ X1 ZERO/C)) (cons σ X2)]
            [(eq? 'Proved (⊢ σ X2 ZERO/C)) (cons σ X1)]
            [else
             (let-values ([(σ L)
                           (σ+ σ
                               (cond [(all-prove? σ V* INT/C) INT/C]
                                     [(all-prove? σ V* REAL/C) REAL/C]
                                     [else NUM/C])
                               (cond [(all-prove? σ V* POS/C) POS/C]
                                     [(all-prove? σ V* NEG/C) NEG/C]
                                     [(all-prove? σ V* NON-NEG/C) NON-NEG/C]
                                     [(all-prove? σ V* NON-POS/C) NON-POS/C]
                                     [else #f])
                               (+/C X1 X2))])
               (cons σ L))]))])]
    [('- (list V1 V2))
     (match (for/list: : (Listof .V) ([Vi V*]) (σ@ σ Vi))
       [(list (.// (.b (? number? x)) _) (.// (.b (? number? y)) _)) (cons σ (Prim (- x y)))]
       [(list (and W1 (.// U1 _)) (and W2 (.// U2 _)))
        (let ([X1 (if (.•? U1) V1 W1)]
              [X2 (if (.•? U2) V2 W2)])
          (cond
            [(and (.L? X1) (.L? X2) (equal? X1 X2)) (cons σ ZERO)]
            [(eq? 'Proved (⊢ σ X2 ZERO/C)) (cons σ X1)]
            [else
             (let-values ([(σ L)
                           (σ+ σ
                               (cond [(all-prove? σ V* INT/C) INT/C]
                                     [(all-prove? σ V* REAL/C) REAL/C]
                                     [else NUM/C])
                               (-/C X1 X2))])
               (cons σ L))]))])]
    [('sqrt (list V))
     (match (for/list: : (Listof .V) ([Vi V*]) (σ@ σ Vi))
       [(list (.// (.b (? real? x)) _)) (cons σ (Prim (sqrt x)))]
       [(list (and W (.// U _)))
        (let ([X (if (.•? U) V W)])
          (cond
            [(eq? 'Proved (⊢ σ X ZERO/C)) (cons σ ZERO)]
            [else
             (let-values ([(σ L)
                           (σ+ σ
                               (cond [(equal? 'Proved (⊢ σ V POS/C)) {set REAL/C POS/C}]
                                     [(equal? 'Proved (⊢ σ V NON-NEG/C)) {set REAL/C NON-NEG/C}]
                                     [(equal? 'Proved (⊢ σ V NEG/C)) {set NUM/C (.¬/C REAL/C)}]
                                     [else NUM/C])
                               (sqrt/C V))])
             (cons σ L))]))])]
    [('< (list (.L i) (.L i))) (cons σ FF)]
    [('< (list V1 V2))
     (match (for/list: : (Listof .V) ([Vi V*]) (σ@ σ Vi))
       [(list (.// (.b (? real? x)) _) (.// (.b (? real? y)) _)) (cons σ (Prim (< x y)))]
       [(list (and W1 (.// U1 _)) (and W2 (.// U2 _)))
        (let ([X1 (if (.•? U1) V1 W1)]
              [X2 (if (.•? U2) V2 W2)])
          (match (⊢ σ X1 (</C X2))
            ['Proved (cons σ TT)]
            ['Refuted (cons σ FF)]
            ['Neither
             (match (⊢ σ X2 (>/C X1))
               ['Proved (cons σ TT)]
               ['Refuted (cons σ FF)]
               ['Neither
                (match-let*
                    ([(cons σt _)
                      (match* (X1 X2)
                        [((.L i) (.L j))
                         (if (> i j) (refine σ X1 (</C X2)) (refine σ X2 (>/C X1)))]
                        [((.L _) _) (refine σ X1 (</C X2))]
                        [(_ (.L _)) (refine σ X2 (>/C X1))]
                        [(_ _) (cons σ 'ignore)])]
                     [(cons σf _)
                      (match* (X1 X2)
                        [((.L i) (.L j))
                         (if (> i j) (refine σ X1 (≥/C X2)) (refine σ X2 (≤/C X1)))]
                        [((.L _) _) (refine σ X1 (≥/C X2))]
                        [(_ (.L _)) (refine σ X2 (≤/C X1))]
                        [(_ _) (cons σ 'ignore)])])
                  {set (cons σt TT) (cons σf FF)})])]))])]
    [('> (list V1 V2)) (Δ σ '< (list V2 V1))]
    [('> (list (.L i) (.L i))) (cons σ FF)]
    [('>= (list (.L i) (.L i))) (cons σ TT)]
    [('>= (list V1 V2)) (match/Vns* (Δ σ '< (list V1 V2))
                           [(cons σt (.// (.b #t) _)) (cons σt FF)]
                           [(cons σf (.// (.b #f) _)) (cons σf TT)])]
    [('<= (list (.L i) (.L i))) (cons σ TT)]
    [('<= (list V1 V2)) (Δ σ '>= (list V2 V1))]
    [('= (list (.L i) (.L i))) (cons σ TT)]
    [('= (list V1 V2))
     (match (for/list: : (Listof .V) ([Vi V*]) (σ@ σ Vi))
       [(list (.// (.b (? number? x)) _) (.// (.b (? number? y)) _)) (cons σ (Prim (= x y)))]
       [(list (and W1 (.// U1 _)) (and W2 (.// U2 _)))
        (let ([X1 (if (.•? U1) V1 W1)]
              [X2 (if (.•? U2) V2 W2)])
          (match (⊢ σ X1 (=/C X2))
            ['Proved (cons σ TT)]
            ['Refuted (cons σ FF)]
            ['Neither
             (match (⊢ σ X2 (=/C X1))
               ['Proved (cons σ TT)]
               ['Refuted (cons σ FF)]
               ['Neither
                (match-let*
                    ([(cons σt _)
                      (match* (X1 X2)
                        [((.L i) (.L j))
                         (if (> i j) (refine σ X1 (=/C X2)) (refine σ X2 (=/C X1)))]
                        [((.L _) _) (refine1 σ X1 (=/C X2))]
                        [(_ (.L _)) (refine1 σ X2 (=/C X1))]
                        [(_ _) (cons σ 'ignore)])]
                     [(cons σf _)
                      (match* (X1 X2)
                        [((.L i) (.L j))
                         (if (> i j) (refine σ X1 (≠/C X2)) (refine σ X2 (≠/C X1)))]
                        [((.L _) _) (refine1 σ X1 (≠/C X2))]
                        [(_ (.L _)) (refine1 σ X2 (≠/C X1))]
                        [(_ _) (cons σ 'ignore)])])
                  {set (cons σt TT) (cons σf FF)})])]))])]
    
    [('string-length (list V))
     (match (σ@ σ V)
       [(.// (.b (? string? s)) _) (cons σ (Prim (string-length s)))]
       [_ (let-values ([(σ L) (σ+ σ INT/C NON-NEG/C)])
            (cons σ L))])]))

(: V=? : .σ .V .V → .Vns*)
(define (V=? σ V1 V2)
  (match* (V1 V2)
    [((.L i) (.L i)) (cons σ TT)]
    [((.L i) (and (.// (not (? .•?)) _) V2))
     (match/Vns* (V=? σ (σ@ σ i) V2)
       [(cons σt (.// (.b #t) _)) (cons (σ-set σ i V2) TT)]
       [a a])]
    [((and (.// (not (? .•?)) _) V1) (.L i))
     (match/Vns* (V=? σ V1 (σ@ σ i))
       [(cons σt (.// (.b #t) _)) (cons (σ-set σ i V1) TT)]
       [a a])]
    [(_ (.L i)) (V=? σ V1 (σ@ σ i))]
    [((.L i) _) (V=? σ (σ@ σ i) V2)]
    [(_ (.// '• _)) {set (cons σ TT) (cons σ FF)}]
    [((.// '• _) _) {set (cons σ TT) (cons σ FF)}]
    [((.// (.St t1 V1*) _) (.// (.St t2 V2*) _))
     (if (eq? t1 t2)
         (let loop ([σ σ] [V1* V1*] [V2* V2*])
           (match* (V1* V2*)
             [('() '()) (cons σ TT)]
             [((cons V1 V1r) (cons V2 V2r))
              (match/Vns* (V=? σ V1 V2)
                [(cons σt (.// (.b #t) _)) (loop σt V1* V2*)]
                [a a])]))
         (cons σ FF))]
    ; default
    [((.// U1 _) (.// U2 _)) (cons σ (Prim (equal? U1 U2)))]))

(: refine : .σ .V (U (Setof .V) (Listof .V) .V) * → .Vns)
(define (refine σ V . C**)
  (: go : .σ .V (Listof (U (Setof .V) (Listof .V) .V)) → .Vns)
  (define (go σ V C**)
    #;(printf "REFINE:~n~a~n~a~n~a~n~n" σ V C**)
    (match C**
      ['() (cons σ V)]
      [(cons (? list? C*) Cr*)
       (match-let ([(cons σ′ V′) (for/fold: ([σV : .Vns (cons σ V)]) ([C : .V C*])
                                   (match-let ([(cons σ V) σV])
                                     (refine σ V C)))])
         (go σ′ V′ Cr*))]
      [(cons (? set? C*) Cr*)
       (match-let ([(cons σ′ V′) (for/fold: ([σV : .Vns (cons σ V)]) ([C : .V C*])
                                   (match-let ([(cons σ V) σV])
                                     (refine σ V C)))])
         (go σ′ V′ Cr*))]
      [(cons (? .V? C) Cr*)
       (match (⊢ σ V C)
         ['Proved (cons σ V)]
         ['Refuted (error "Bogus refinement")]
         [_ (match-let ([(cons σ′ V′) (refine1 σ V C)])
              (go σ′ V′ Cr*))])]))
  (go σ V C**))

(: refine1 : .σ .V .V → .Vns)
(define (refine1 σ V C)
  (let ([C (simplify C)])
     
    (when (match? C (.// '• _)) (error "ha!"))
    (match V
      [(.L i) (match-let ([(cons σ′ V′) (refine1 σ (σ@ σ i) C)])
                (match V′
                  [(.// (.St t V*) C*) (match-let* ([(cons σ′ V*′) (alloc σ′ V*)]
                                                    [V′ (.// (.St t V*′) C*)])
                                         (cons (σ-set σ′ i V′) V))]
                  [(? .//? V′) (cons (σ-set σ′ i V′) V)]
                  [_ (error "broken =_=" V)]))]
      [(.// U C*)
       (match C
         [(.L _) (cons σ (.// U (set-add C* C)))]
         [(.// Uc _)          
          (match Uc
            [(.St 'and/c (list C1 C2)) (refine σ V C1 C2)]
            [(.St 'or/c (list C1 C2))
             #;(begin
               (define ¬mt (.¬/C (Prim 'empty?)))
               (define ¬cons (.¬/C (Prim 'cons?)))
               (when (equal? C1 (Prim 'empty?))))
             (match* ((⊢ σ V C1) (⊢ σ V C2))
               [('Refuted 'Refuted) (error "WTF??")]
               [(_ 'Refuted) (refine1 σ V C1)]
               [('Refuted _) (refine1 σ V C2)]
               [(_ _) (refine-U σ U (refine-C* C* C))])]
            [(? .μ/C? Uc) (refine1 σ V (unroll/C Uc))]
            ; equal contracts
            [(.λ↓ (.λ 1 (.@ (or '= 'equal?) (list (.x 0) e) _) #f) ρ)
             (match e
               [(? .b? b) (cons σ (.// b C*))]
               [(and (? .λ? f) (? closed?)) (cons σ (.// (.λ↓ f ρ∅) C*))]
               [(.x i) (match (ρ@ ρ (- i 1))
                         [(.L a) (match-let ([(.// U′ C*′) (σ@ σ a)])
                                   (cons σ (.// (U+ U U′) (∪ C* C*′ C))))]
                         [(.// U′ C*′) (cons σ (.// (U+ U U′) (∪ C* C*′)))])]
               [_ (refine-U σ U (refine-C* C* C))])]
            ; struct contracts
            [(.St/C t D*)
             (match-let*-values ([(σ V*)
                                  (match U
                                    ['• (σ++ σ (length D*))]
                                    [(.St _ V*) (values σ V*)])]
                                 [((cons σ V*)) (refine* σ V* D*)])
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
            [_ (refine-U σ U (refine-C* C* C))])])])))

(: refine-U : .σ .U (Setof .V) → .Vns)
(define (refine-U σ U Cs)
  (define-values (D/st Ds)
    (set-partition (λ ([C : .V]) (match? C (.// (? .St/C?) _))) Cs))
  (if (set-empty? D/st)
      (cons σ (.// U Ds))
      (refine1 σ (.// U Ds) (set-first D/st))))

(: refine* : .σ (Listof .V) (Listof .V) → (Pairof .σ (Listof .V)))
(define (refine* σ V* C*)  
  (let-values ([(σ′ V*′)
                (for/fold: ([σ : .σ σ] [Vs : (Listof .V) '()]) ([V V*] [C C*])
                  #;(printf "Got:~n~a~n~a~n~n" V C)
                  (match-let ([(cons σ V) (refine1 σ V C)])
                    (values σ (cons V Vs))))])
    (cons σ′ (reverse V*′))))

(: check-C : .σ .V .V → .Vns*)
(define (check-C σ V C)
  (match (⊢ σ V C)
    ['Proved (cons σ TT)]
    ['Refuted (cons σ FF)]
    ['Neither (match-let ([(cons σt _) (refine σ V C)]
                          [(cons σf _) (refine σ V (.¬/C C))])
                {set (cons σt TT) (cons σf FF)})]))

(: refine-C* : (Setof .V) .V → (Setof .V))
(define (refine-C* C* C)
  (if (set-empty? C*) {set C}
      (for/fold ([acc : (Setof .V) ∅]) ([Ci C*]) (∪ acc (refine-C Ci C)))))

(: refine-C : .V .V → (U .V (Setof .V)))
(define (refine-C C D)
  (cond
    [(equal? 'Proved (C⇒C C D)) C]
    [(equal? 'Proved (C⇒C D C)) D]
    [else
     (match* (C D)
       [((.// Uc _) (.// Ud _))
        (match* (Uc Ud)
          ; unroll recursive ones
          [(_ (.μ/C x D′)) (refine-C C (C/ D′ x D))]
          [((.μ/C x C′) _) (refine-C (C/ C′ x C) D)]
          ; break conjunctive ones
          [(_ (.St 'and/c (list D1 D2))) (∪ (refine-C C D1) (refine-C C D2))]
          [((.St 'and/c (list C1 C2)) _) (∪ (refine-C C1 D) (refine-C C2 D))]
          ; prune impossible disjunct
          [(_ (.St 'or/c _)) (let ([D′ (truncate D C)])
                               (if (equal? D D′) {set C D} (refine-C C D′)))]
          [((.St 'or/c _) _) (let ([C′ (truncate C D)])
                               (if (equal? C C′) {set C D} (refine-C C′ D)))]
          ; special rules for reals
          [((.λ↓ (.λ 1 (.@ '>= (list e1 e2) l) #f) ρc)
            (.St '¬/c (list (.// (.λ↓ (.λ 1 (.@ (or '= 'equal?)
                                                (or (list e1 e2) (list e2 e1)) _) #f) ρd) _))))
           (if (equal? ρc ρd) (→V (.λ↓ (.λ 1 (.@ '> (list e1 e2) l) #f) ρc)) {set C D})]
          [((.St '¬/c (list (.// (.λ↓ (.λ 1 (.@ (or '= 'equal?)
                                                (or (list e1 e2) (list e2 e1)) _) #f) ρc) _)))
            (.λ↓ (.λ 1 (.@ '>= (list e1 e2) l) #f) ρd))
           (if (equal? ρc ρd) (→V (.λ↓ (.λ 1 (.@ '> (list e1 e2) l) #f) ρd)) {set C D})]
          [((.λ↓ (.λ 1 (.@ '<= (list e1 e2) l) #f) ρc)
            (.St '¬/c (list (.// (.λ↓ (.λ 1 (.@ (or '= 'equal?)
                                                (or (list e1 e2) (list e2 e1)) _) #f) ρd) _))))
           (if (equal? ρc ρd) (→V (.λ↓ (.λ 1 (.@ '< (list e1 e2) l) #f) ρc)) {set C D})]
          [((.St '¬/c (list (.// (.λ↓ (.λ 1 (.@ (or '= 'equal?)
                                                (or (list e1 e2) (list e2 e1)) _) #f) ρc) _)))
            (.λ↓ (.λ 1 (.@ '<= (list e1 e2) l) #f) ρd))
           (if (equal? ρc ρd) (→V (.λ↓ (.λ 1 (.@ '< (list e1 e2) l) #f) ρd)) {set C D})]
          [(_ _) {set C D}])]
       [(_ _) {set C D}])]))

;; throws away all branch in C excluded by D
(: truncate : .V .V → .V)
(define (truncate C D)
  (match C
    [(.// (.St 'or/c (list C1 C2)) C*)
     (match* ((C⇒C D C1) (C⇒C D C2))
       [('Refuted 'Refuted) (error "WTF??")]
       [(_ 'Refuted) (truncate C1 D)]
       [('Refuted _) (truncate C2 D)]
       [(_ _) (.// (.St 'or/c (list (truncate C1 D) (truncate C2 D))) C*)])]
    [_ C]))

(: U+ : .U .U → .U)
(define U+ (match-lambda** [('• U) U] [(U _) U]))

(: ∪ : (U (Setof .V) .V) * → (Setof .V))
(define (∪ . V*)
  (match V*
    ['() ∅]
    [(list (? .V? V)) {set V}]
    [(list (? set? V)) V]
    [_ (for/fold ([acc : (Setof .V) ∅]) ([V V*])
         (if (set? V) (set-union acc V) (set-add acc V)))]))

(: U^ : .U → (Setof .V))
(define U^
  (match-lambda [(.b b) (b^ b)]
                ['• ∅]
                [(or (? .Ar?) (? .λ↓?)) {set PROC/C}]
                [(.St t V*) {set (→V (.st-p t (length V*)))}]
                [_ ∅]))

(: b^ : (U Number String Symbol Boolean) → (Setof .V))
(define b^
  (match-lambda
    [(? integer? n) (set-union {set (Prim 'integer?) (Prim 'real?) (Prim 'number?)} (sign/C n))]
    [(? real? r) (set-union {set (Prim 'real?) (Prim 'number?)} (sign/C r))]
    [(? number? x) {set (Prim 'number?)}]
    [(? string?) {set (Prim 'string?)}]
    [(? symbol?) {set (Prim 'symbol?)}]
    [#t {set (Prim 'true?) (Prim 'boolean?)}]
    [#f {set (Prim 'false?) (Prim 'boolean?)}]))


(: alloc : (case→ [.σ .V → .Vns]
                  [.σ (Listof .V) → (Pairof .σ (Listof .V))]))
(define (alloc σ V)
  (match V
    [(.L _) (cons σ V)]
    [(.// (.St t V*) Cs) (match-let ([(cons σ V*′) (alloc σ V*)])
                           (cons σ (.// (.St t V*′) Cs)))]
    [(.// (.Ar C V l^3) Cs) (match-let ([(cons σ V′) (alloc σ V)])
                              (cons σ (.// (.Ar C V′ l^3) Cs)))]
    [(.// (.λ↓ f (.ρ m l)) Cs)
     (let-values ([(σ m)
                   (for/fold: ([σ : .σ σ] [m′ : (Map (U Integer Symbol) .V) m]) ([x (in-hash-keys m)])
                     (match-let ([(cons σ V) (alloc σ (hash-ref m x))])
                       (values σ (hash-set m′ x V))))])
       (cons σ (→V (.λ↓ f (.ρ m l)))))]
    [(.// '• Cs)
     (let-values ([(σ L) (σ+ σ)])
       (refine σ L Cs))]
    [(? .V? V) (cons σ V)]
    [(? list? V*)
     (let-values ([(σ Vs)
                   (for/fold ([σ : .σ σ] [Vs : (Listof .V) '()]) ([V V*])
                     (match-let ([(cons σ V) (alloc σ V)])
                       (values σ (cons V Vs))))])
       (cons σ (reverse Vs)))]))
