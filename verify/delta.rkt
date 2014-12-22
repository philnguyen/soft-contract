#lang typed/racket/base
(require racket/match racket/set racket/list racket/function racket/bool
         "../utils.rkt" "../lang.rkt" "../runtime.rkt" "../provability.rkt" "../show.rkt")
(provide (all-defined-out))

(define-syntax-rule (match/Ans* v [p e ...] ...) (match/nd: (.Ans → .Ans) v [p e ...] ...))
(define-syntax-rule (match/Vns* v [p e ...] ...) (match/nd: (.Vns → .Vns) v [p e ...] ...))

(: δ : .σ .o (Listof .V) Sym → .Ans*)
(define (δ σ o V* l)
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
    [((.=) (list V1 V2))
     (match/Ans* (δ σ (.num?) (list V1) 'Λ)
       [(cons σt (.// (.b #t) _))
        (match/Ans* (δ σt (.num?) (list V2) 'Λ)
          [(cons σt (.// (.b #t) _)) (Δ σt (.=) V*)]
          [(cons σf (.// (.b #f) _)) (cons σf (.blm l '= V2 NUM/C))])]
       [(cons σf (.// (.b #f) _)) (cons σf (.blm l '= V1 NUM/C))])]
    [((or (.add1) (.sub1)) (list V))
     (match/Ans* (δ σ (.num?) V* 'Λ)
       [(cons σt (.// (.b #t) _)) (Δ σt o V*)]
       [(cons σf (.// (.b #f) _)) (cons σf (.blm l (name o) V NUM/C))])]
    [((or (.+) (.-) (.*)) (list V1 V2))
     (match/Ans* (δ σ (.num?) (list V1) 'Λ)
       [(cons σt (.// (.b #t) _))
        (match/Ans* (δ σt (.num?) (list V2) 'Λ)
          [(cons σt (.// (.b #t) _)) (Δ σt o V*)]
          [(cons σf (.// (.b #f) _)) (cons σf (.blm l (name o) V2 NUM/C))])]
       [(cons σf (.// (.b #f) _)) (cons σf (.blm l (name o) V1 NUM/C))])]
    [((.+) (list)) (cons σ (Prim 0))]
    [((.*) (list)) (cons σ (Prim 1))]
    [((or (.+) (.*)) (list V))
     (match/Ans* (δ σ (.num?) (list V) 'Λ)
       [(cons σt (.// (.b #t) _)) (cons σt V)]
       [(cons σf (.// (.b #f) _)) (cons σf V)])]
    [((or (.+) (.*)) (list* V₁ V₂ Vᵣ))
     (match/Ans* (δ σ o (list V₁ V₂) l)
       [(cons σ (? .V? Vᵢ)) (δ σ o (cons Vᵢ Vᵣ) l)]
       [(and ans (cons σ (? .blm?))) ans])]
    [((./) (list V1 V2))
     (match/Ans* (δ σ (.num?) (list V1) 'Λ)
       [(cons σt (.// (.b #t) _))
        (match/Ans* (δ σt (.num?) (list V2) 'Λ)
          [(cons σt (.// (.b #t) _))
           (match/Ans* (δ σt (.=) (list V2 (Prim 0)) 'Λ)
             [(cons σt (.// (.b #t) _)) (cons σt (.blm l '/ V2 NON-ZERO/C))]
             [(cons σf (.// (.b #f) _)) (Δ σf (./) V*)])]
          [(cons σf (.// (.b #f) _)) (cons σf (.blm l '/ V2 NUM/C))])]
       [(cons σf (.// (.b #f) _)) (cons σf (.blm l '/ V1 NUM/C))])]
    [((or (.>) (.<) (.≤) (.≥)) (list V1 V2))
     (match/Ans* (δ σ (.real?) (list V1) 'Λ)
       [(cons σt (.// (.b #t) _))
        (match/Ans* (δ σt (.real?) (list V2) 'Λ)
          [(cons σt (.// (.b #t) _)) (Δ σt o V*)]
          [(cons σf (.// (.b #f) _)) (cons σf (.blm l (name o) V2 REAL/C))])]
       [(cons σf (.// (.b #f) _)) (cons σf (.blm l (name o) V1 REAL/C))])]
    [((.str-len) (list V))
     (match/Ans* (δ σ (.str?) V* 'Λ)
       [(cons σt (.// (.b #t) _)) (Δ σt (.str-len) V*)]
       [(cons σf (.// (.b #f) _)) (cons σf (.blm l 'str-len V STR/C))])]
    [((.equal?) (list V1 V2)) (V=? σ V1 V2)]
    [((.sqrt) (list V))
     (match/Ans* (δ σ (.real?) (list V) 'Λ)
       [(cons σt (.// (.b #t) _)) (Δ σt (.sqrt) V*)]
       [(cons σf (.// (.b #f) _)) (cons σf (.blm l 'sqrt V REAL/C))])]
    
    ; arity check
    [((or (.arity=?) (.arity≥?) (.arity-includes?)) (list V1 V2))
     (match/Ans* (δ σ (.proc?) (list V1) 'Λ)
       [(cons σt (.// (.b #t) _))
        (match/Ans* (δ σt (.int?) (list V2) 'Λ)
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
    [((.add1) (list V)) (Δ σ (.+) (list V ONE))]
    [((.sub1) (list V)) (Δ σ (.-) (list V ONE))]
    
    [((.*) (list V1 V2))
     (match (for/list: : (Listof .V) ([Vi V*]) (σ@ σ Vi))
       [(list (.// (.b (? num? x)) _) (.// (.b (? num? y)) _)) (cons σ (Prim (* x y)))]
       [(list (and W1 (.// U1 _)) (and W2 (.// U2 _)))
        (let ([X1 (if (.•? U1) V1 W1)]
              [X2 (if (.•? U2) V2 W2)])
          (cond
            [(eq? 'Proved (⊢ σ X1 ZERO/C)) (cons σ ZERO)]
            [(eq? 'Proved (⊢ σ X2 ZERO/C)) (cons σ ZERO)]
            [(eq? 'Proved (⊢ σ X1 ONE/C)) (cons σ X2)]
            [(eq? 'Proved (⊢ σ X2 ONE/C)) (cons σ X1)]
            [else (let-values ([(σ V)
                                (σ+ σ
                                    (cond [(all-prove? σ V* INT/C) INT/C]
                                          [(all-prove? σ V* REAL/C) REAL/C]
                                          [else NUM/C])
                                    (cond [(all-prove? σ V* POS/C) POS/C]
                                          [(all-prove? σ V* NON-NEG/C) NON-NEG/C]
                                          [(all-prove? σ V* NON-ZERO/C) NON-ZERO/C]
                                          [else #f])
                                    (*/C X1 X2))])
                    (cons σ V))]))])]
    [((./) (list V1 V2))
     (match (for/list: : (Listof .V) ([Vi V*]) (σ@ σ Vi))
       [(list (.// (.b (? num? x)) _) (.// (.b (? num? y)) _)) (cons σ (Prim (/ x y)))]
       [(list (and W1 (.// U1 _)) (and W2 (.// U2 _)))
        (let ([X1 (if (.•? U1) V1 W1)]
              [X2 (if (.•? U2) V2 W2)])
          (cond
            [(eq? 'Proved (⊢ σ X1 ZERO/C)) (cons σ ZERO)]
            [else (let-values ([(σ V)
                                (σ+ σ
                                    (cond [(all-prove? σ V* REAL/C) REAL/C]
                                          [else NUM/C])
                                    (cond [(all-prove? σ V* POS/C) POS/C]
                                          [(all-prove? σ V* NON-NEG/C) NON-NEG/C]
                                          [(eq? 'Proved (⊢ σ V1 NON-ZERO/C)) NON-ZERO/C]
                                          [else #f])
                                    (÷/C X1 X2)
                                    (if (eq? 'Proved (⊢ σ X1 NON-ZERO/C)) NON-ZERO/C #f))])
                    (cons σ V))]))])]
    [((.+) (list V1 V2))
     (match (for/list: : (Listof .V) ([Vi V*]) (σ@ σ Vi))
       [(list (.// (.b (? num? x)) _) (.// (.b (? num? y)) _)) (cons σ (Prim (+ x y)))]
       [(list (and W1 (.// U1 _)) (and W2 (.// U2 _)))
        (let ([X1 (if (.•? U1) V1 W1)]
              [X2 (if (.•? U2) V2 W2)])
          (cond
            [(eq? 'Proved (⊢ σ X1 ZERO/C)) (cons σ X2)]
            [(eq? 'Proved (⊢ σ X2 ZERO/C)) (cons σ X1)]
            [else (let-values ([(σ V)
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
                    (cons σ V))]))])]
    [((.-) (list V1 V2))
     (match (for/list: : (Listof .V) ([Vi V*]) (σ@ σ Vi))
       [(list (.// (.b (? num? x)) _) (.// (.b (? num? y)) _)) (cons σ (Prim (- x y)))]
       [(list (and W1 (.// U1 _)) (and W2 (.// U2 _)))
        (let ([X1 (if (.•? U1) V1 W1)]
              [X2 (if (.•? U2) V2 W2)])
          (cond
            [(and (.L? X1) (.L? X2) (equal? X1 X2)) (cons σ ZERO)]
            [(eq? 'Proved (⊢ σ X2 ZERO/C)) (cons σ X1)]
            [else (let-values ([(σ V)
                                (σ+ σ
                                    (cond [(all-prove? σ V* INT/C) INT/C]
                                          [(all-prove? σ V* REAL/C) REAL/C]
                                          [else NUM/C])
                                    (-/C X1 X2))])
                    (cons σ V))]))])]
    [((.sqrt) (list V))
     (match (for/list: : (Listof .V) ([Vi V*]) (σ@ σ Vi))
       [(list (.// (.b (? real? x)) _)) (cons σ (Prim (sqrt x)))]
       [(list (and W (.// U _)))
        (let ([X (if (.•? U) V W)])
          (cond
            [(eq? 'Proved (⊢ σ X ZERO/C)) (cons σ ZERO)]
            [else (let-values ([(σ V)
                                (σ+ σ
                                    (cond [(equal? 'Proved (⊢ σ V POS/C)) {set REAL/C POS/C}]
                                          [(equal? 'Proved (⊢ σ V NON-NEG/C)) {set REAL/C NON-NEG/C}]
                                          [(equal? 'Proved (⊢ σ V NEG/C)) {set NUM/C (.¬/C REAL/C)}]
                                          [else NUM/C])
                                    (sqrt/C V))])
                    (cons σ V))]))])]
    [((.<) (list (.L i) (.L i))) (cons σ FF)]
    [((.<) (list V1 V2))
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
    [((.>) (list V1 V2)) (Δ σ (.<) (list V2 V1))]
    [((.>) (list (.L i) (.L i))) (cons σ FF)]
    [((.≥) (list (.L i) (.L i))) (cons σ TT)]
    [((.≥) (list V1 V2)) (match/Vns* (Δ σ (.<) (list V1 V2))
                           [(cons σt (.// (.b #t) _)) (cons σt FF)]
                           [(cons σf (.// (.b #f) _)) (cons σf TT)])]
    [((.≤) (list (.L i) (.L i))) (cons σ TT)]
    [((.≤) (list V1 V2)) (Δ σ (.≥) (list V2 V1))]
    [((.=) (list (.L i) (.L i))) (cons σ TT)]
    [((.=) (list V1 V2))
     (match (for/list: : (Listof .V) ([Vi V*]) (σ@ σ Vi))
       [(list (.// (.b (? num? x)) _) (.// (.b (? num? y)) _)) (cons σ (Prim (= x y)))]
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
    
    [((.str-len) (list V))
     (match (σ@ σ V)
       [(.// (.b (? str? s)) _) (cons σ (Prim (string-length s)))]
       [_ (let-values ([(σ V) (σ+ σ INT/C NON-NEG/C)])
            (cons σ V))])]))

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
    [(_ (.// (.•) _)) {set (cons σ TT) (cons σ FF)}]
    [((.// (.•) _) _) {set (cons σ TT) (cons σ FF)}]
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
    #;(printf "refine1:~n~a~n~a~n~a~n~n" (show-σ σ) (show-E σ V) (show-E σ C))
    (when (match? C (.// (.•) _)) (error "ha!"))
    (match V
      [(.L i) (match-let ([(cons σ′ V′) (refine1 σ (σ@ σ i) C)])
                (match V′
                  [(.// (.St t V*) C*) (match-let* ([(cons σ′ V*′) (alloc σ′ V*)]
                                                    [V′ (.// (.St t V*′) C*)])
                                         (cons (σ-set σ′ i V′) V))]
                  [(? .//? V′) (cons (σ-set σ′ i V′) V)]
                  [(? .μ/V? V′) (cons (σ-set σ′ i V′) V)] ; duplicate to get around TR
                  [_ (error "broken =_=" V)]))
              #;(match (refine1 σ (σ@ σ i) C)
                [(cons σ (? .L? L)) (cons σ L)]
                [(cons σ′ V′) (if (or (.//? V′) (.μ/V? V′))
                                  (cons (σ-set σ′ i V′) V)
                                  (error "broken: " V′))])]
      [(.// U C*)
       (match C
         [(.L _) (cons σ (.// U (set-add C* C)))]
         [(.// Uc _)          
          (match Uc
            [(.St 'and/c (list C1 C2)) (refine σ V C1 C2)]
            [(.St 'or/c (list C1 C2))
             (match* ((⊢ σ V C1) (⊢ σ V C2))
               [('Refuted 'Refuted) (error "WTF??")]
               [(_ 'Refuted) (refine1 σ V C1)]
               [('Refuted _) (refine1 σ V C2)]
               [(_ _) (cons σ (.// U (refine-C* C* C)))])]
            [(and Uc (.μ/C x C′))
             (match U
               [(.•) (cons σ (reify C))]
               [(.St t V*) (refine1 σ V (unroll/C Uc))]
               [_ (cons σ V)])]
            ; equal contracts
            [(.λ↓ (.λ 1 (.@ (or (.=) (.equal?)) (list (.x 0) e) _) #f) ρ)
             (match e
               [(? .b? b) (cons σ (.// b C*))]
               [(and (? .λ? f) (? closed?)) (cons σ (.// (.λ↓ f ρ∅) C*))]
               [(.x i) (match (ρ@ ρ (- i 1))
                         [(.L a) (match-let ([(.// U′ C*′) (σ@ σ a)])
                                   (cons σ (.// (U+ U U′) (∪ C* C*′ C))))]
                         [(.// U′ C*′) (cons σ (.// (U+ U U′) (∪ C* C*′)))])]
               [_ (cons σ (.// U (set-add C* C)))])]
            ; struct contracts
            [(.St/C t D*)
             (match-let* ([(cons σ V*) (ann (match U
                                              [(.•)
                                               (let-values ([(σ Vs) (σ++ σ (length D*))])
                                                 (cons σ Vs))]
                                              [(.St _ V*) (cons σ V*)])
                                            (Pairof .σ (Listof .V)))]
                          [(cons σ V*) (refine* σ V* D*)])
               (cons σ (.// (.St t V*) C*)))]
            [(.st-p t n) (match U
                           [(.•)
                            (let-values ([(σ′ L*) (σ++ σ n)])
                              (cons σ′ (.// (.St t L*) C*)))]
                           [(.St (? (curry eq? t)) _) (cons σ V)])]
            ; singleton contracts
            [(.true?) (cons σ (.// .tt C*))]
            [(.false?) (cons σ (.// .ff C*))]
            [(.st-p t 0) (cons σ (.// (.St t '()) C*))]
            [_ (cons σ (.// U (set-add C* C)))])])]
      [(and (.μ/V x V*) V)
       (let*-values ([(σ′ V*′)
                      (for/fold: ([σ : .σ σ] [Vs : (Setof .V) ∅]) ([Vi V*])
                        (match (⊢ σ Vi C)
                          ['Proved (values σ (set-add Vs Vi))]
                          ['Refuted (values σ Vs)]
                          ['Neither (match-let* ([(cons σ′ Vj) (refine1 σ Vi C)]
                                                 [(cons Vj′ Vs′) (elim-μ x Vj)])
                                      (values σ′ (compact (compact Vs Vs′) {set Vj′})))]))])
         #;(printf "new V* is ~a~n~n" (for/set: Any ([Vi V*′]) (show-V σ′ Vi)))
         (match (set-count V*′)
           [0 (error "bogus refinement") #;V∅]
           [1 (cons σ′ (V/ (set-first V*′) (.X/V x) V))]
           [_ (cons σ′ (μV x V*′))]))]
      [(? .X/V? x) (cons σ x)]))) ; abuse μ for non-inductive set

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
      (for/fold: ([acc : (Setof .V) ∅]) ([Ci C*]) (∪ acc (refine-C Ci C)))))

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
          [((.λ↓ (.λ 1 (.@ (.≥) (list e1 e2) l) #f) ρc)
            (.St '¬/c (list (.// (.λ↓ (.λ 1 (.@ (or (.=) (.equal?))
                                                (or (list e1 e2) (list e2 e1)) _) #f) ρd) _))))
           (if (equal? ρc ρd) (→V (.λ↓ (.λ 1 (.@ (.>) (list e1 e2) l) #f) ρc)) {set C D})]
          [((.St '¬/c (list (.// (.λ↓ (.λ 1 (.@ (or (.=) (.equal?))
                                                (or (list e1 e2) (list e2 e1)) _) #f) ρc) _)))
            (.λ↓ (.λ 1 (.@ (.≥) (list e1 e2) l) #f) ρd))
           (if (equal? ρc ρd) (→V (.λ↓ (.λ 1 (.@ (.>) (list e1 e2) l) #f) ρd)) {set C D})]
          [((.λ↓ (.λ 1 (.@ (.≤) (list e1 e2) l) #f) ρc)
            (.St '¬/c (list (.// (.λ↓ (.λ 1 (.@ (or (.=) (.equal?))
                                                (or (list e1 e2) (list e2 e1)) _) #f) ρd) _))))
           (if (equal? ρc ρd) (→V (.λ↓ (.λ 1 (.@ (.<) (list e1 e2) l) #f) ρc)) {set C D})]
          [((.St '¬/c (list (.// (.λ↓ (.λ 1 (.@ (or (.=) (.equal?))
                                                (or (list e1 e2) (list e2 e1)) _) #f) ρc) _)))
            (.λ↓ (.λ 1 (.@ (.≤) (list e1 e2) l) #f) ρd))
           (if (equal? ρc ρd) (→V (.λ↓ (.λ 1 (.@ (.<) (list e1 e2) l) #f) ρd)) {set C D})]
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
(define U+ (match-lambda** [((.•) U) U] [(U _) U]))

(: ∪ : (U (Setof .V) .V) * → (Setof .V))
(define (∪ . V*)
  (match V*
    ['() ∅]
    [(list (? .V? V)) {set V}]
    [(list (? set? V)) V]
    [_ (for/fold: ([acc : (Setof .V) ∅]) ([V V*])
         (if (set? V) (set-union acc V) (set-add acc V)))]))

(: U^ : .U → (Setof .V))
(define U^
  (match-lambda [(.b b) (b^ b)]
                [(.•) ∅]
                [(or (? .Ar?) (? .λ↓?)) {set PROC/C}]
                [(.St t V*) {set (→V (.st-p t (length V*)))}]
                [_ ∅]))

(: b^ : (U Num Str Sym Bool) → (Setof .V))
(define b^
  (match-lambda
    [(? int? n) (set-union {set (Prim 'integer?) (Prim 'real?) (Prim 'number?)} (sign/C n))]
    [(? real? r) (set-union {set (Prim 'real?) (Prim 'number?)} (sign/C r))]
    [(? num? x) {set (Prim 'number?)}]
    [(? str?) {set (Prim 'string?)}]
    [(? sym?) {set (Prim 'symbol?)}]
    [#t {set (Prim 'true?) (Prim 'boolean?)}]
    [#f {set (Prim 'false?) (Prim 'boolean?)}]))

(: v-class : .σ (U .V (Setof .V)) → (Setof Any))
(define (v-class σ x)
  (match x
    [(.L i) (v-class σ (σ@ σ i))]
    [(.// U C*)
     (match U
       [(.•) (or (for/or: : (Option (Setof Any)) ([C : .V C*] #:when (match? C (.// (.pred) _)))
                   (match-let ([(.// (and o (.pred)) _) C])
                     {set (name o)}))
                 {set '•})]
       [(? .o? o) {set `(prim ,(name o))}]
       [(.b u) {set (cond
                      [(int? u) 'int?]
                      [(real? u) 'real?]
                      [(num? u) 'num?]
                      [(str? u) 'str?]
                      [(false? #f) 'false?]
                      [(eq? u #t) 'true?]
                      [(sym? u) 'sym?]
                      [else 'misc])}]
       [(.Ar _ V _) (v-class σ V)]
       [(.St t _) {set t}]
       [(.λ↓ (.λ n _ v?) _) {set `(proc? ,n ,v?)}]
       [_ {set 'misc}])]
    [(.μ/V _ V*) (v-class σ V*)]
    [(.X/V _) ∅]
    [(? set? s) (for/fold: ([acc : (Setof Any) ∅]) ([i s])
                  (set-union acc (v-class σ i)))]))

;; biased approximation
(: ⊕ : (case→ 
        [.σ .V .σ .V → (Pairof .σ .V)]
        [.σ (Listof .V) .σ (Listof .V) → (Pairof .σ (Listof .V))]
        [.σ .σ .F → .σ]
        [.V .V → .V]
        [(Listof .V) (Listof .V) → (Listof .V)]
        [.ρ .ρ → .ρ]))
(define ⊕
  #;(printf "⊕:~n~n~a~n~nand~n~n~a~n~n~n" V0 V1)
  (case-lambda
    [(σ0 V0 σ1 V1)
     (match* (V0 V1)
       [((? .V? V0) (? .V? V1))
        (match-let ([Vi (⊕ (V-abs σ0 V0) (V-abs σ1 V1))])
          (match V1
            [(.L i) (match-let ([(cons σ1′ Vi′) (alloc σ1 Vi)])
                      (match Vi′
                        [(.L j) (cons (σ-set σ1′ i (σ@ σ1′ j)) V1)]
                        [(and Vi′ (or (? .//?) (? .μ/V?))) (cons (σ-set σ1′ i Vi′) V1)]
                        [_ (error "⊕: impossible: .X/V")]))]
            [_ (alloc σ1 Vi)]))
        #;(let ([Vi (⊕ (V-abs σ0 V0) (V-abs σ1 V1))])
          (cond
            [(or (.//? Vi) (.μ/V? Vi))
             (match V1
               [(.L i) (cons (σ-set σ1 i Vi) V1)]
               [_ (cons σ1 Vi)])]
            [else (error "⊕: impossible")]))]
       [((? list? V0) (? list? V1))
        (match-let ([(cons σ1′ l-rev)
                     (for/fold: ([acc : (Pairof .σ (Listof .V)) (cons σ1 '())]) ([V0i V0] [V1i V1])
                       (match-let* ([(cons σ1 l) acc]
                                    [(cons σ1′ Vi) (⊕ σ0 V0i σ1 V1i)])
                         (cons σ1′ (cons Vi l))))])
          (cons σ1′ (reverse l-rev)))])]
    [(σ0 σ1 F)
     (for/fold: : .σ ([σ1 : .σ σ1]) ([i (in-hash-keys F)])
       (let* ([j (hash-ref F i)])
         (match (⊕ (V-abs σ0 (σ@ σ0 i)) (V-abs σ1 (σ@ σ1 i)))
           [(and V (or (? .//?) (? .μ/V?))) (σ-set σ1 j V)]
           [_ (error "⊕: impossible")])))]
    [(x y)
     (match* (x y)
       ; same-length lists expected
       [((? list? V0) (? list? V1)) (map ⊕ V0 V1)]
       ; values
       [((? .V? V0) (? .V? V1))
        #;(printf "⊕:~n~a~nand~n~a~n~n" (show-Ans σ∅ V0) (show-Ans σ∅ V1))
        #;(printf "⊕:~n~a~nand~n~a~n~n" V0 V1)
        (let: ([ans : .V (cond
          [(V∈ V1 V0) V1] ; postpone approximation if value shrinks
          #;[(and (.//? V1) (.•? (.//-pre V1)) (= 1 (set-count (.//-refine V1)))) V1]
          #;[(equal? V0 ♦) ♦]
          [(⊑ V1 V0) V0]
          [(⊑ V0 V1) V1]
          [else
           (match* (V0 V1)
             [((.// U0 C*) (.// U1 D*))
              (match* (U0 U1)
                ; keep around common values: 0, 1, #t, #f, struct with no component
                [(_ (or (.•) (? .o?) (.b 0) (.b 1) (.b #t) (.b #f) (.St _ '()))) V1]
                ; cannot blur higher order value
                [(_ (.λ↓ f ρ))
                 (let ([repeated (repeated-lambdas f ρ)])
                   (match (set-count repeated)
                     [0 V1]
                     ; TODO: μ introduced outside here. Am i sure there's none inside?
                     [_ (let ([V′ (μV 'X (set-add repeated (for/fold: ([V1 : .V V1]) ([Vi repeated])
                                                             (V/ V1 Vi (.X/V 'X)))))])
                          #;(printf "~a~n⇒⊕~n~a~n~n" V1 V′)
                          V′)]))]
                [((.Ar C V0 l) (.Ar C V1 l))
                 (.// (.Ar C (⊕ V0 V1) l) D*)]
                [(_ (or (? .λ?) (? .Ar?))) V1]
                [((.St t V0*) (.St t V1*)) (.// (.St t (⊕ V0* V1*)) D*)]
                [(_ (.St t V1*)) #;(printf "⊕:case1~n")
                                 #;(printf "⊕:~n~a~nand~n~a~n~n" (show-E σ∅ V0) (show-E σ∅ V1))
                                 (match-let* ([x 'X #;(fresh V1*)]
                                              [Vi* (V/ V1* V0 (.X/V x))]
                                              [(cons Vi* Vs) (elim-μ x Vi*)])
                                   (if (equal? Vi* V1*) (.// • (set-intersect C* D*))
                                       #;(μV x (compact {set V0 (.// (.St t Vi*) D*)} Vs))
                                       (.// (.St t (V/ Vi* (.X/V x) (μV x (compact {set V0 (.// (.St t Vi*) ∅)} Vs)))) D*)))]
                [((.b (? num? b0)) (.b (? num? b1)))
                 (cond ; if it moves towards 0, let it take its time
                   #;[(and (int? b0) (int? b1) (or (<= 0 b1 b0) (>= 0 b1 b0))) V1]
                   [else
                    (.// • (set-add
                            (cond [(and (real? b0) (real? b1))
                                   {set (cond [(and (> b0 0) (> b1 0)) POS/C]
                                              [(and (< b0 0) (< b1 0)) NEG/C]
                                              [(and (not (= b0 0)) (not (= b1 0))) NON-ZERO/C]
                                              [(and (>= b0 0) (>= b1 0)) NON-NEG/C]
                                              [(and (<= b0 0) (<= b1 0)) NON-POS/C]
                                              [else REAL/C])}]
                                  [else ∅])
                            (cond [(and (int? b0) (int? b1)) INT/C]
                                  [(and (real? b0) (real? b1)) REAL/C]
                                  [else NUM/C])))])]
                [(_ _)
                 (let ([C* (set-union C* (U^ U0))])
                   (.// • (for/set: .V ([D (set-union D* (U^ U1))]
                                        #:when (eq? 'Proved (C*⇒C C* D)))
                            D)))])]
             [((.μ/V x V0*) (.μ/V y V1*)) #;(printf "⊕:case2~n") (μV x (compact V0* (V/ V1* (.X/V y) (.X/V x))))]
             [((.μ/V x V0*) _)
              #;(printf "⊕:case3~n")
              #;(printf "~a  ∩  ~a~n~n" (v-class σ∅ V0*) (v-class σ∅ V1))
              (if (set-empty? (set-intersect (v-class σ∅ V0*) (v-class σ∅ V1)))
                  V1
                  (match-let ([(cons V1′ Vs) (dbg/off 'case3 (elim-μ x (V/ V1 V0 (.X/V x))))])
                (μV x (dbg/off 'compact1 (compact (dbg/off 'compact0 (compact V0* {set V1′})) Vs)))))]
             [(_ (.μ/V x V1*))
              #;(printf "⊕:case4~n")
              #;(printf "~a  ∩  ~a~n~n" (v-class σ∅ V0) (v-class σ∅ V1*))
              (if (set-empty? (set-intersect (v-class σ∅ V0) (v-class σ∅ V1*)))
                  V1
                  (match-let ([(cons V0′ Vs) (elim-μ x (V/ V0 V1 (.X/V x)))])
                    (μV x (compact (compact {set V0′} Vs) V1*))))]
             [((? .X/V? x) _) x]
             [(_ (? .X/V? x)) x])])])
          #;(printf "⊕:~n~a~nand~n~a~nis~n~a~n~n" (show-Ans σ∅ V0) (show-Ans σ∅ V1) (show-Ans σ∅ ans))
          (check ans)
          ans)]
       [((and ρ0 (.ρ m0 l0)) (and ρ1 (.ρ m1 l1)))
        (let* ([l (max l0 l1)]
               [m (for/fold: ([m : (Map (U Int Sym) .V) (hash)]) ([sd (in-range 0 l)])
                    (match* ((hash-ref m0 (- l0 sd 1) (λ () #f))
                             (hash-ref m1 (- l1 sd 1) (λ () #f)))
                      [(#f #f) m]
                      [(#f (? .V? V)) (hash-set m (- l sd 1) V)]
                      [((? .V? V) #f) (hash-set m (- l sd 1) V)]
                      [((? .V? V0) (? .V? V1)) (hash-set m (- l sd 1) (⊕ V0 V1))]))]
               [m (for/fold: ([m : (Map (U Int Sym) .V) m]) ([k (in-hash-keys m0)] #:when (sym? k))
                    (hash-set m k (hash-ref m0 k)))]
               [m (for/fold: ([m : (Map (U Int Sym) .V) m]) ([k (in-hash-keys m1)] #:when (sym? k))
                    (hash-set m k (hash-ref m1 k)))])
          (.ρ m l))])]))

(: check : (case→ [.V → Void]
                  [.V Int → Void]))
(define (check V [i 1])
  (match V
    [(.μ/V _ V*) (if (<= i 0) (error "no!") (for ([Vi V*]) (check Vi (- i 1))))]
    [(.// (.St _ V*) _) (for ([Vi V*]) (check Vi))]
    [_ (void)]))

;; remove all sub-μ. TODO: generalize allowed μ-depth
(: elim-μ : (case→ [Sym .V → (Pairof .V (Setof .V))]
                   [Sym (Listof .V) → (Pairof (Listof .V) (Setof .V))]))
(define (elim-μ x V)
  (define-set: body* : .V [_ add!])
  (: go : (case→ [.V → .V] [(Listof .V) → (Listof .V)]))
  (define go
    (match-lambda
      [(? list? V*) (map go V*)]
      [(? .L? V) V]
      [(and V (.// U1 C*))
       (match U1
         [(.St t V*) (.// (.St t (map go V*)) C*)]
         [(.Ar C V l) (.// (.Ar C (go V) l) C*)]
         [(.λ↓ f (and ρ (.ρ m l)))
          #;(printf "elim-μ: ρ:~n~a~n~n" m)
          (let ([m′ (for/fold: ([m′ : (Map (U Int Sym) .V) m∅]) ([x (in-hash-keys m)])
                      (hash-set m′ x (go (hash-ref m x))))])
            (if (equal? m′ m) V (.// (.λ↓ f (.ρ m′ l)) C*)))]
         [_ V])]
      [(.μ/V z V*) (add! (for/set: .V ([Vi V*]) (V/ Vi (.X/V z) (.X/V x)))) (.X/V x)]
      [(.X/V _) (.X/V x)]))
  
  (let ([V′ (go V)])
    #;(printf "elim-μ depth ~a → ~a~n~n" (μ-depth V) (μ-depth V′))
    (cons V′ body*)))

; remove redundant variable
; simplify to • if body has •
(: μV : Sym (Setof .V) → .V)
(define (μV x V*)
  #;(for ([Vi V*]) (check Vi 0))
  (let ([V* (for/set: .V ([V V*] #:unless (equal? V (.X/V x))) V)])
    (cond
      [(set-member? V* ♦) ♦]
      [else (match (set-count V*)
              [0 V∅]
              [1 (let* ([V (set-first V*)]
                        [V′ (V/ V (.X/V x) (.X/V '☠))])
                   (if (equal? V V′) V V∅))]
              [_ (.μ/V x V*)])])))

; group values together by top constructors
(: compact : (Setof .V) (Setof .V) → (Setof .V))
(define (compact V0s V1s)
  #;(printf "compact:~n~n~a~nand~n~a~n~n~n" V0s V1s)
  #;(printf "depth: ~a, ~a~n~n"
          (for/list: : (Listof Int) ([V V0s]) (μ-depth V))
          (for/list: : (Listof Int) ([V V1s]) (μ-depth V)))
  (: collect : (Setof .V) → (Values (Map Any .V) (Setof .X/V)))
  (define (collect Vs)
    #;(printf "collect:~n~a~n~n" Vs)
    (for/fold: ([m : (Map Any .V) (hash)] [xs : (Setof .X/V) ∅]) ([V Vs])
      (match V
        [(.// U C*)
         (match U
           [(.b (? num?)) (values (hash-set m 'num? V) xs)]
           [(.b (? str?)) (values (hash-set m 'str? V) xs)]
           [(.b (? sym?)) (values (hash-set m 'sym? V) xs)]
           [(.b #t) (values (hash-set m #t V) xs)]
           [(.b #f) (values (hash-set m #f V) xs)]
           [(? .o? o) (values (hash-set m `(o ,(name o)) V) xs)]
           [(.•) (values (hash-set m (for/fold: : Any ([ac '•]) ([C C*])
                                       (match C
                                         [(.// (? .pred? p) _) (match p
                                                                 [(.st-p t _) t]
                                                                 [_ (name p)])]
                                         [_ ac]))
                                   V)
                         xs)]
           [(or (? .Ar?) (? .λ↓?) (.o)) (values (hash-set m 'proc? V) xs)] ; TODO: by arity also?
           [(.St t _) (values (hash-set m `(struct ,t) V) xs)])]
        [(? .μ/V? V) (error (format "weird:~n~a~n~a~n~n" V0s V1s)) (values (hash-set m 'μ V) xs)]
        [(? .X/V? x) (values m (set-add xs x))])))
  
  (: merge : (.V .V → (Pairof .V (Setof .V))))
  (define (merge V0 V1)
    (match* (V0 V1)
      [((? .X/V? x) V1) (cons x (match V1 [(.X/V _) ∅] [_ {set V1}]))]
      [((.// (.St t V0*) C*) (.// (.St t V1*) D*))
       (let-values ([(q V*)
                     (for/fold: ([q : (Setof .V) ∅] [V* : (Listof .V) '()]) ([Vi V0*] [Vj V1*])
                       (match-let ([(cons V′ q′) (merge Vi Vj)])
                         (values (set-union q q′) (cons V′ V*))))])
         (cons (.// (.St t (reverse V*)) (set-intersect C* D*)) q))]
      [(_ _) (match (⊕ V0 V1) ; FIXME hack
               [(and V (.μ/V x V*)) (elim-μ x V)]
               [V (cons V ∅)])]))  
  
  (: go : (Setof .V) (Setof .V) → (Setof .V))
  (define (go V0s V1s)
    #;(printf "go:~n~a~n~nand~n~n~a~n~n~n" V0s V1s)
    (let-values ([(m0 xs) (collect V0s)]
                 [(m1 zs) (collect V1s)])
      (let: ([q : (Setof .V) ∅])
        (let ([s0 (for/set: .V ([k (in-hash-keys m0)])
                    (let ([V0 (hash-ref m0 k)])
                      (match (hash-ref m1 k (λ () #f))
                        [#f V0]
                        [(? .V? V1) (match-let ([(cons V′ q′) (dbg/off 'go (merge V0 V1))])
                                      (set! q (set-union q q′))
                                      V′)])))]
              [s1 (for/set: .V ([k (in-hash-keys m1)] #:unless (hash-has-key? m0 k))
                    (hash-ref m1 k))])
          (let* ([s (set-union s0 s1)])
            (if (subset? q s) s
                (begin #;(printf "q: ~a~n~ns:~a~n~n"
                               (for/set: Any ([x q]) (show-V σ∅ x))
                               (for/set: Any ([x s]) (show-V σ∅ x)))
                       (go s q))))))))
  
  (go V0s V1s))

(: μ-depth : (case→ [.V → Int] [(Listof .V) → (Listof Int)]))
(define μ-depth
  (match-lambda
    [(? list? V*) (map μ-depth V*)]
    [(.// (.St _ V*) _) (apply max (map μ-depth V*))]
    [(.μ/V _ V*) (+ 1 (for/fold: : Int ([l 0]) ([V V*]) (max l (μ-depth V))))]
    [(? .V?) 0]))

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
                   (for/fold: ([σ : .σ σ] [m′ : (Map (U Int Sym) .V) m]) ([x (in-hash-keys m)])
                     (match-let ([(cons σ V) (alloc σ (hash-ref m x))])
                       (values σ (hash-set m′ x V))))])
       (cons σ (→V (.λ↓ f (.ρ m l)))))]
    [(.// (.•) Cs)
     (let-values ([(σ L) (σ+ σ)])
       (refine σ L Cs))]
    [(? .μ/V? V)
     (let-values ([(σ L) (σ+ σ)])
       (cons (σ-set σ L V) L))]
    [(? .V? V) (cons σ V)]
    [(? list? V*) (let-values ([(σ Vs)
                                (for/fold: ([σ : .σ σ] [Vs : (Listof .V) '()]) ([V V*])
                                  (match-let ([(cons σ V) (alloc σ V)])
                                    (values σ (cons V Vs))))])
                    (cons σ (reverse Vs)))]))

(: refine-V : .V .V → .V)
(define (refine-V V C)
  (match-let* ([(cons σ V) (alloc σ∅ V)]
               [(cons σ V) (refine1 σ V C)])
    (V-abs σ V)))

(: reify : .V → .V)
(define (reify C)
  (match C
    [(.L _) (.// • {set C})]
    [(.// Uc _)
     (match Uc
       [(.St 'and/c (list C1 C2)) (refine-V (reify C1) C2)]
       [(.St 'or/c (list C1 C2))
        (match* ((reify C1) (reify C2))
          [((.μ/V x V1*) (.μ/V z V2*)) (μV x {set-union V1* (V/ V2* (.X/V z) (.X/V x))})]
          [((and V1 (.μ/V x V1*)) V2) (μV x (set-add V1* (V/ V2 V1 (.X/V x))))]
          [(V1 (and V2 (.μ/V x V2*))) (μV x (set-add V2* (V/ V1 V2 (.X/V x))))]
          [(V1 V2) (if (equal? V1 V2) V1 (μV '_ {set V1 V2}))])]
       [(.St/C t D*) (→V (.St t (map reify D*)))]
       [(.μ/C x D) (match (reify D)
                     [(.μ/V '_ V*) (μV x V*)]
                     [(? .V? V) V])]
       [(and Uc (.Λ/C C* D v?)) (→V (.Ar (→V Uc) ♦ `(Λ Λ Λ) #|FIXME|#))]
       [(.X/C x) (.X/V x)]
       [(.st-p t n) (→V (.St t (make-list n ♦)))]
       [(.λ↓ (.λ 1 (.b #t) #f) _) ♦]
       [_ (.// • {set (simplify C)})])]))

