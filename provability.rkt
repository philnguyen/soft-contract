#lang typed/racket/base
(require racket/match racket/set racket/list
         "utils.rkt" "lang.rkt" "runtime.rkt" "show.rkt"
         (only-in "query-z3.rkt" [query z3]))
(provide (all-defined-out))

(:* all-prove? all-refute? some-proves? some-refutes? : .σ (Listof .V) .V → Boolean)
(define (all-prove? σ V* C) (for/and ([V V*]) (eq? (⊢ σ V C) '✓)))
(define (all-refute? σ V* C) (for/and ([V V*]) (eq? (⊢ σ V C) 'X)))
(define (some-proves? σ V* C) (for/or ([V V*]) (eq? (⊢ σ V C) '✓)))
(define (some-refutes? σ V* C) (for/or ([V V*]) (eq? (⊢ σ V C) 'X)))

(define ext-solver (make-parameter z3))

(: ⊢ : .σ .V .V → .R)
(define (⊢ σ V C)
  ;;(printf "⊢:~nV:~a~nC:~a~n~n" V C #;(show-E σ V) #;(show-E σ C))
  (let ([C (simplify C)])
    (match (⊢′ σ V C)
      ['? ((ext-solver) σ V C)]
      [r #;(printf "Ans: ~a~n~n" r) r])))

;; Integerernal, lightweight, lo-tech prover
(: ⊢′ : (case→ [.σ .V .V → .R]
               [.σ .U .V → .R]
               [.σ .U .U → .R]))
(define (⊢′ σ V C)
  (define-set assumed : (Pairof (U .U .V) (U .U .V)))
  
  ;; just for debugging
  (: show : .σ (U .V .U) → Any)
  (define (show σ x)
    (if (.V? x) (show-V σ x) (show-U σ x)))
  
  (: go : (case→ [.V .V → .R] [.U .V → .R] [.U .U → .R]))
  (define (go V C)
    (cond
     [(assumed-has? (cons V C)) '✓]
     [else
      (match* (V C)
        ; V ∈ C
        [((.L i) C)
         (match C ; HACK
           [(.// (.λ↓ (.λ 1 (.@ (or '= 'equal?) (list-no-order (.x 0) (.x a)) _)) ρ) _)
            (match (ρ@ ρ (- (cast a Integer) 1))
              [(.L j) (if (= i j) '✓ (go (σ@ σ i) C))]
              [_ (go (σ@ σ i) C)])]
           [_ (go (σ@ σ i) C)])]
        [((.// U C*) C) (match (go U C)
                          ['? (C*⇒C C* C)]
                          [r r])]
        [((and V (.μ/V x V*)) C)
         (assumed-add! (cons V C))
         (let ([r (for/set: : (Setof .R) ([V (unroll V)]) (go V C))])
           (match (set-count r) ; TODO optimize?
             [0 '✓]
             [1 (set-first r)]
             [_ (cond
                 [(for/and: : Boolean ([ri r]) (equal? ri '✓)) '✓]
                 [(for/and: : Boolean ([ri r]) (equal? ri 'X)) 'X]
                 [else '?])]))]
        [((.X/V x) C) '✓]
        
        ; U ∈ C
        [((? .U? U) (? .V? C))
         (match C
           [(.L _) '?]
           [(.// Uc _) (go U Uc)])]
        
        ; U ∈ U
        [(_ (.λ↓ (.λ _ (.b #t)) _)) '✓] ; any
        [(_ (.λ↓ (.λ _ (.b #f)) _)) 'X] ; none
        [('• _) '?] ; opaque, no further info
        [((? .U? U) (? .U? Uc))
         (match* (U Uc)
           ;; negation
           [(_ (.St 'not/c (list C′))) (¬R (go U C′))]
           [(_ (.λ↓ (.λ n (.@ 'false? (list e) l)) ρ)) (¬R (go U (.λ↓ (.λ n e) ρ)))]
           
           ;; base predicates as contracts
           [([.b (? number?)] 'number?) '✓]
           [([.b (? real?)] 'real?) '✓]
           [([.b (? integer?)] 'integer?) '✓]
           [([.b (? string?)] 'string?) '✓]
           [([.b (? boolean?)] 'boolean?) '✓]
           [([.b #t] 'true?) '✓]
           [([.b #f] 'false?) '✓]
           [([.b symbol?] 'symbol?) '✓]
           
           ;; proc
           [((or (? .λ↓?) (? .Ar?) (? .o?) (? .Case?)) 'procedure?) '✓]
           ;; struct
           [((.St t _) (.st-p t _)) '✓]
           [((.St t V*) (.St/C t C*))
            (for/fold ([r : .R '✓]) ([Vi V*] [Ci C*])
              (match r
                ['X 'X]
                [_ (match (go Vi Ci)
                     ['✓ r]
                     ['X 'X]
                     ['? '?])]))]
           
           ;; definite retutes for other concrete values
           [((not (? .λ↓?) (? .Ar?) (? .o?) (? .Case?)) 'procedure?) 'X]
           [(_ (? .St/C?)) 'X]
           [(_ (? .pred?)) 'X]
           
           ;; special rules for reals. Had to split cases because TR doesn't play well with (or ...)
           [((.b b1) (.λ↓ (.λ 1 (.@ (or '= 'equal?)
                                    (or (list (.x 0) (.b b2)) (list (.b b2) (.x 0))) _)) _))
            (decide-R (equal? b1 b2))]
           [((.b (? real? r1)) (.λ↓ (.λ 1 (.@ '>= (list (.x 0) (.b (? real? r2))) _)) _))
            (decide-R (>= r1 r2))]
           [((.b (? real? r1)) (.λ↓ (.λ 1 (.@ '<= (list (.b (? real? r2)) (.x 0)) _)) _))
            (decide-R (>= r1 r2))]
           [((.b (? real? r1)) (.λ↓ (.λ 1 (.@ '> (list (.x 0) (.b (? real? r2))) _)) _))
            (decide-R (> r1 r2))]
           [((.b (? real? r1)) (.λ↓ (.λ 1 (.@ '< (list (.b (? real? r2)) (.x 0)) _)) _))
            (decide-R (> r1 r2))]
           [((.b (? real? r1)) (.λ↓ (.λ 1 (.@ '<= (list (.x 0) (.b (? real? r2))) _)) _))
            (decide-R (<= r1 r2))]
           [((.b (? real? r1)) (.λ↓ (.λ 1 (.@ '>= (list (.b (? real? r2)) (.x 0)) _)) _))
            (decide-R (<= r1 r2))]
           [((.b (? real? r1)) (.λ↓ (.λ 1 (.@ '< (list (.x 0) (.b (? real? r2))) _)) _))
            (decide-R (< r1 r2))]
           [((.b (? real? r1)) (.λ↓ (.λ 1 (.@ '> (list (.b (? real? r2)) (.x 0)) _)) _))
            (decide-R (< r1 r2))]
           
           ;; rules for arities
           ;; arity includes
           [(_ (.λ↓ (.λ 1 (.@ 'arity-includes? (list (.x 0) (.b (? integer? n))) _)) _))
            (match U
              [(.λ↓ (.λ m _) _) (decide-R (= m n))]
              [(.Ar (.// (.Λ/C Cx _ v?) _) _ _)
               (if v? (decide-R (>= n (- (length Cx) 1))) (decide-R (= n (length Cx))))]
              [(? .o1?) (decide-R (= n 1))]
              [(? .o2?) (decide-R (= n 2))]
              [(.st-mk _ m) (decide-R (= m n))]
              [(.Case m) (cond
                          [(for/or : Boolean ([k (in-hash-keys m)])
                             (= (length k) n))
                           '✓]
                          [else '?])]
              [_ '?])]
           ;; arity at least
           [(_ (.λ↓ (.λ 1 (.@ 'arity>=? (list (.x 0) (.b (? integer? n))) _)) _))
            (match U
              [(.λ↓ (.λ m _) _) 'X]
              [(.Ar (.// (.Λ/C Cx _ v?) _) _ _) (if v? (decide-R (>= n (- (length Cx) 1))) 'X)]
              [(? .o?) 'X]
              [_ '?])]
           ;; arity exact
           [(_ (.λ↓ (.λ 1 (.@ 'arity=? (list (.x 0) (.b (? integer? n))) _)) _))
            (match U
              [(.λ↓ (.λ m _) _) (decide-R (= m n))]
              [(.Ar (.// (.Λ/C Cx _ v?) _) _ _) (if v? 'X (decide-R (= (length Cx) n)))]
              [(? .o1?) (decide-R (= n 1))]
              [(? .o2?) (decide-R (= n 2))]
              [(.st-mk _ m) (decide-R (= m n))]
              [_ '?])]
           
           
           ;; conjunctive, disjunctive, and recursive contracts
           [(_ (.St 'and/c (list P Q)))
            (match (go U P)
              ['X 'X]
              ['✓ (go U Q)]
              ['? (match (go U Q) ['X 'X] [_ '?])])]
           [(_ (.St 'or/c (list P Q)))
            (match (go U P)
              ['✓ '✓]
              ['X (go U Q)]
              ['? (match (go U Q) ['✓ '✓] [_ '?])])]
           [(_ (and Uc (.μ/C x C′))) (assumed-add! (cons V C)) (go U (unroll/C Uc))]
           
           ;; conservative default
           [(_ _) '?])])]))
  (go V C))

(: C*⇒C*? : (Setof .V) (Setof .V) → Boolean)
(define (C*⇒C*? Cs Ds)
  (for/and ([D Ds]) (eq? '✓ (C*⇒C Cs D))))

(: C*⇒C : (Setof .V) .V → .R)
(define (C*⇒C C* C)  
  (match C
    [(.// (.St 'and/c (list C1 C2)) _) (∧R (C*⇒C C* C1) (C*⇒C C* C2))]
    [_ (for*/fold: ([R : .R '?]) ([Ci C*])
         (match (C⇒C (simplify Ci) C) ; FIXME: can't use for/first with #:when
           ['✓ '✓]
           ['X 'X]
           ['? R]))]))

; checks whether first contract proves second
(: C⇒C : .V .V → .R)
(define (C⇒C C D)
  #;(printf "C:~n~a~nD:~n~a~n~n" C D)
  (let go ([C C] [D D] [assume : (Setof (Pairof .V .V)) ∅])
    (cond
      [(C≃ C D) '✓]
      [(set-member? assume (cons C D)) '✓]
      [else
       (match* (C D)
         [((.// Uc _) (.// Ud _))
          (match* (Uc Ud)
            [(_ (.λ↓ (.λ _ (.b #t)) _)) '✓] ; any
            [(_ (.λ↓ (.λ _ (.b #f)) _)) 'X] ; none
            [((? .pred? o1) (? .pred? o2)) (p⇒p o1 o2)] ; primitive predicates
            
            ;; eliminate negation
            [((.St 'not/c (list C′)) (.St 'not/c (list D′)))
             (match (go D′ C′ assume)
               ['✓ '✓]
               [_ '?])]
            [((.St 'not/c (list C′)) _)
             (match (go D C′ assume)
               ['✓ 'X]
               [_ '?])]
            [(_ (.St 'not/c (list D′))) (¬R (go C D′ assume))]
            
            ;; special rules for reals
            [((.λ↓ (.λ 1 (.@ '> (list (.x 0) (.b (? real? r1))) _)) _)
              (.λ↓ (.λ 1 (.@ (or '> '>=) (list (.x 0) (.b (? real? r2))) _)) _))
             (if (>= r1 r2) '✓ '?)]
            [((.λ↓ (.λ 1 (.@ '> (list (.x 0) (.b (? real? r1))) _)) _)
              (.λ↓ (.λ 1 (.@ (or '= '< '<=) (list (.x 0) (.b (? real? r2))) _)) _))
             (if (>= r1 r2) 'X '?)]
            
            [((.λ↓ (.λ 1 (.@ '>= (list (.x 0) (.b (? real? r1))) _)) _)
              (.λ↓ (.λ 1 (.@ '> (list (.x 0) (.b (? real? r2))) _)) _))
             (if (> r1 r2) '✓ '?)]
            [((.λ↓ (.λ 1 (.@ '>= (list (.x 0) (.b (? real? r1))) _)) _)
              (.λ↓ (.λ 1 (.@ '>= (list (.x 0) (.b (? real? r2))) _)) _))
             (if (>= r1 r2) '✓ '?)]
            [((.λ↓ (.λ 1 (.@ '>= (list (.x 0) (.b (? real? r1))) _)) _)
              (.λ↓ (.λ 1 (.@ (or '<= '=) (list (.x 0) (.b (? real? r2))) _)) _))
             (if (> r1 r2) 'X '?)]
            [((.λ↓ (.λ 1 (.@ '>= (list (.x 0) (.b (? real? r1))) _)) _)
              (.λ↓ (.λ 1 (.@ '< (list (.x 0) (.b (? real? r2))) _)) _))
             (if (>= r1 r2) 'X '?)]
            
            [((.λ↓ (.λ 1 (.@ '= (list (.x 0) (.b (? real? r1))) _)) _)
              (.λ↓ (.λ 1 (.@ o (list (.x 0) (.b (? real? r2))) _)) _))
             (decide-R ((match o ['= =] ['> >] ['< <] ['>= >=] ['<= <=]) r1 r2))]
            
            [((.λ↓ (.λ 1 (.@ '<= (list (.x 0) (.b (? real? r1))) _)) _)
              (.λ↓ (.λ 1 (.@ '< (list (.x 0) (.b (? real? r2))) _)) _))
             (if (< r1 r2) '✓ '?)]
            [((.λ↓ (.λ 1 (.@ '<= (list (.x 0) (.b (? real? r1))) _)) _)
              (.λ↓ (.λ 1 (.@ '<= (list (.x 0) (.b (? real? r2))) _)) _))
             (if (<= r1 r2) '✓ '?)]
            [((.λ↓ (.λ 1 (.@ '<= (list (.x 0) (.b (? real? r1))) _)) _)
              (.λ↓ (.λ 1 (.@ (or '>= '=) (list (.x 0) (.b (? real? r2))) _)) _))
             (if (< r1 r2) 'X '?)]
            [((.λ↓ (.λ 1 (.@ '<= (list (.x 0) (.b (? real? r1))) _)) _)
              (.λ↓ (.λ 1 (.@ '> (list (.x 0) (.b (? real? r2))) _)) _))
             (if (<= r1 r2) 'X '?)]
            
            [((.λ↓ (.λ 1 (.@ '< (list (.x 0) (.b (? real? r1))) _)) _)
              (.λ↓ (.λ 1 (.@ (or '< '<=) (list (.x 0) (.b (? real? r2))) _)) _))
             (if (<= r1 r2) '✓ '?)]
            [((.λ↓ (.λ 1 (.@ '< (list (.x 0) (.b (? real? r1))) _)) _)
              (.λ↓ (.λ 1 (.@ (or '= '> '>=) (list (.x 0) (.b (? real? r2))) _)) _))
             (if (<= r1 r2) 'X '?)]
            
            [((.λ↓ (.λ 1 (.@ (or '> '< '>= '<=) (list (.x 0) _) _)) _) (or 'real? 'number?)) '✓]
            [((.λ↓ (.λ 1 (.@ '= (list (.x 0) _) _)) _) 'number?) '✓]
            
            ;; struct
            [((.st-p t n) (.St/C t _)) (if (= n 0) '✓ '?)]
            [((.St/C t _) (.st-p t n)) (if (= n 0) '✓ '?)]
            [((.St/C t C*) (.St/C t D*))
             (for/fold ([a : .R '✓]) ([Ci C*] [Di D*])
               (match a
                 ['X 'X]
                 [_ (match (go Ci Di assume) ['✓ a] [r r])]))]
            [((or (? .St/C?) (? .st-p?)) (or (? .pred?) (? .St/C?))) 'X]
            [('procedure? (or (? .St/C?) (? .st-p?) (? .pred?))) 'X]
            
            ;; recursive contracts
            [((.μ/C x C′) (.μ/C y D′)) (go (C/ C′ x C) (C/ D′ y D) (set-add assume (cons C D)))]
            [((.μ/C x C′) _) (go (C/ C′ x C) D (set-add assume (cons C D)))]
            [(_ (.μ/C y D′)) (go C (C/ D′ y D) (set-add assume (cons C D)))]
            
            ;; rules for arity
            ;; arity exact
            [((.λ↓ (.λ 1 (.@ 'arity=? (list (.x 0) (.b (? integer? m))) _)) _)
              (.λ↓ (.λ 1 (.@ 'arity=? (list (.x 0) (.b (? integer? n))) _)) _))
             (decide-R (= m n))]
            [((.λ↓ (.λ 1 (.@ 'arity>=? (list (.x 0) (.b (? integer? m))) _)) _)
              (.λ↓ (.λ 1 (.@ 'arity=? (list (.x 0) (.b (? integer? n))) _)) _))
             'X]
            [((.λ↓ (.λ 1 (.@ 'arity-includes? (list (.x 0) (.b (? integer? m))) _)) _)
              (.λ↓ (.λ 1 (.@ 'arity=? (list (.x 0) (.b (? integer? n))) _)) _))
             (if (= m n) '? 'X)]
            ;; arity at least
            [((.λ↓ (.λ 1 (.@ 'arity=? (list (.x 0) (.b (? integer? m))) _)) _)
              (.λ↓ (.λ 1 (.@ 'arity>=? (list (.x 0) (.b (? integer? n))) _)) _))
             'X]
            [((.λ↓ (.λ 1 (.@ 'arity>=? (list (.x 0) (.b (? integer? m))) _)) _)
              (.λ↓ (.λ 1 (.@ 'arity>=? (list (.x 0) (.b (? integer? n))) _)) _))
             (if (>= m n) '✓ '?)]
            [((.λ↓ (.λ 1 (.@ 'arity-includes? (list (.x 0) (.b (? integer? m))) _)) _)
              (.λ↓ (.λ 1 (.@ 'arity>=? (list (.x 0) (.b (? integer? n))) _)) _))
             '?]
            ;; arity includes
            [((.λ↓ (.λ 1 (.@ 'arity=? (list (.x 0) (.b (? integer? m))) _)) _)
              (.λ↓ (.λ 1 (.@ 'arity-includes? (list (.x 0) (.b (? integer? n))) _)) _))
             (decide-R (= m n))]
            [((.λ↓ (.λ 1 (.@ 'arity>=? (list (.x 0) (.b (? integer? m))) _)) _)
              (.λ↓ (.λ 1 (.@ 'arity-includes? (list (.x 0) (.b (? integer? n))) _)) _))
             (if (>= n m) '✓ '?)]
            [((.λ↓ (.λ 1 (.@ 'arity-includes? (list (.x 0) (.b (? integer? m))) _)) _)
              (.λ↓ (.λ 1 (.@ 'arity-includes? (list (.x 0) (.b (? integer? n))) _)) _))
             (if (= m n) '✓ '?)]
            
            ;; break apart composit contracts
            [((.St 'or/c (list C1 C2)) _)
             (match* ((go C1 D assume) (go C2 D assume))
               [('✓ '✓) '✓]
               [('X 'X) 'X]
               [(_ _) '?])]
            [(_ (.St 'and/c (list D1 D2))) (∧R (go C D1 assume) (go C D2 assume))]
            [(_ (.St 'or/c (list D1 D2))) (∨R (go C D1 assume) (go C D2 assume))]
            [((.St 'and/c (list C1 C2)) _)
             (match* ((go C1 D assume) (go C2 D assume))
               [('✓ _) '✓]
               [(_ '✓) '✓]
               [('X 'X) 'X]
               [(_ _) '?])]
            [(_ _) '?])] ; default
         [(_ _) '?])]))) ; default

(: p⇒p : .pred .pred → .R)
(define (p⇒p p q)
  (cond
    [(equal? p q) '✓]
    [else
     (match* (p q)
       [((or 'true? 'false?) 'boolean?) '✓]
       [((or 'real? 'integer?) 'number?) '✓]
       [('integer? 'real?) '✓]
       [('boolean? (or 'true? 'false?)) '?]
       [('number? (or 'real? 'integer?)) '?]
       [('real? 'integer?) '?]
       [((.st-p t _) (.st-p t _)) '✓]
       [(_ _) 'X])]))

(: ¬R : .R → .R)
(define ¬R
  (match-lambda ['✓ 'X] ['X '✓] [_ '?]))

(define-syntax ∨R
  (syntax-rules ()
    [(_ e) e]
    [(_ e1 e ...) (match e1
                    ['✓ '✓]
                    ['X (∨R e ...)]
                    ['? (match (∨R e ...) ['✓ '✓] [_ '?])])]))

(define-syntax ∧R
  (syntax-rules ()
    [(_ e) e]
    [(_ e1 e ...) (match e1
                    ['✓ (∧R e ...)]
                    ['X 'X]
                    ['? (match (∧R e ...) ['X 'X] [_ '?])])]))
(: decide-R : Boolean → .R)
(define decide-R (match-lambda [#t '✓] [#f 'X]))

(: ⊑ : (case→ [.σ .σ → (case→
                        [.V .V → (Option .F)]
                        [(Listof .V) (Listof .V) → (Option .F)]
                        [.ρ .ρ → (Option .F)])]
              [.V .V → (Option .F)]
              [(Listof .V) (Listof .V) → (Option .F)]))
(define ⊑
  (match-lambda**
      [((? .σ? σ0) (? .σ? σ1))
       (define F : .F (hash))
       (define-set assumed : (Pairof .V .V))
       
       (: go! : (case→ [.V .V → Boolean]
                       [(Listof .V) (Listof .V) → Boolean]
                       [.ρ .ρ → Boolean]))
       (define (go! x y)
         #;(printf "go:~nσ0:~n~a~nσ1:~n~a~nV0:~n~a~nV1:~n~a~n~n" σ0 σ1 x y)
         (match* (x y)
           [((? .V? V0) (? .V? V1))
            (or        
             (assumed-has? (cons V0 V1))
             (match* (V0 V1)
               [((.// U0 C*) (.// U1 D*))
                (match* (U0 U1)
                  [('• '•)
                   (C*⇒C*?
                       (for/set: : (Setof .V)
                                 ([C (in-set C*)]
                                  #:unless
                                  (match?
                                   C
                                   (.//
                                    (.λ↓
                                     (.λ 1
                                         (.@ (or '= 'equal?)
                                             (list (.x 0) (not (? .v?) (? .x?))) 'Λ)) _)
                                    _)))
                         C)
                       (for/set: : (Setof .V)
                                 ([D (in-set D*)]
                                  #:unless
                                  (match?
                                   D
                                   (.//
                                    (.λ↓
                                     (.λ 1
                                         (.@ (or '= 'equal?)
                                             (list (.x 0) (not (? .v?) (? .x?))) 'Λ)) _)
                                    _)))
                         D))]
                  [((.St t V0*) (.St t V1*)) (andmap go! V0* V1*)]
                  [((.Ar C1 V1 _) (.Ar C2 V2 _)) (and (equal? C1 C2) (go! V1 V2))]
                  [((.λ↓ e0 ρ0) (.λ↓ e1 ρ1)) (and (equal? e0 e1) (go! ρ0 ρ1))]
                  [(_ '•)
                   (match U0
                     [(.b (? integer?)) (C*⇒C*? (set-add C* INT/C) D*)]
                     [(.b (? real?)) (C*⇒C*? (set-add C* REAL/C) D*)]
                     [(.b (? number?)) (C*⇒C*? (set-add C* NUM/C) D*)]
                     [(.b (? string?)) (C*⇒C*? (set-add C* STR/C) D*)]
                     [(.b (? symbol?)) (C*⇒C*? (set-add C* SYM/C) D*)]
                     [_ (C*⇒C*? C* D*)])]
                  [(_ _) (equal? U0 U1)])]
               [((.L i) (.L j))
                (match (hash-ref F j #f)
                  [#f #;(printf "no key~n")
                      (if (go! (σ@ σ0 i) (σ@ σ1 j))
                          (begin #;(printf "lookedup yes~n")(set! F (hash-set F j i)) #t)
                          #f)]
                  [(? integer? i′) #;(printf "yes key~n")(= i i′)])]
               [((.L i) _) (go! (σ@ σ0 i) V1)]
               [(_ (.L j)) (go! V0 (σ@ σ1 j))]
               [((? .μ/V? V0) (? .μ/V? V1))
                #;(printf "Case0: ~a~n~n~a~n~n" (show-V σ0 V0) (show-V σ1 V1))
                (assumed-add! (cons V0 V1))
                (for/and : Boolean ([V0i (unroll V0)])
                  (for/or : Boolean ([V1i (unroll V1)]) ;FIXME: may screw up F
                    (let ([G F])
                      (or (go! V0i V1i) (begin (set! F G) #f)))))]
               [((? .μ/V? V0) _)
                #;(printf "Case2: ~a~n~n~a~n~n" (show-V σ0 V0) (show-V σ1 V1))
                (assumed-add! (cons V0 V1))
                (for/and ([V0i (unroll V0)]) (go! V0i V1))]
               [(_ (? .μ/V? V1))
                #;(printf "Case1: ~a~n~n~a~n~n" (show-V σ0 V0) (show-V σ1 V1))
                (assumed-add! (cons V0 V1))
                (for/or : Boolean ([V1i (unroll V1)])
                  (let ([G F])
                    (or (go! V0 V1i) (begin (set! F G) #f))))] ; FIXME: may screw up F
               [(_ _) #f]))]
           [((.ρ m0 l0) (.ρ m1 l1))
            (for/and ([i (in-range 0 (max l0 l1))])
              (match* ((hash-ref m0 (- l0 i 1) #f) (hash-ref m1 (- l1 i 1) #f))
                [((? .V? V0) (? .V? V1)) (go! V0 V1)]
                [(#f #f) #t]
                [(_ _) #f]))]
           [((? list? V0*) (? list? V1*)) (andmap go! V0* V1*)]))
       (λ (V0 V1) (if (go! V0 V1) F #f))]
    [((? .V? V0) (? .V? V1)) ((⊑ σ∅ σ∅) V0 V1)]
    [((? list? l0) (? list? l1)) ((⊑ σ∅ σ∅) l0 l1)]))


(: C≃ : (case→ [.V .V → Boolean]
              [.U .U → Boolean]
              [.expr .expr → Boolean]
              [.ρ .ρ → Boolean]))
(define (C≃ x y)
  (match* (x y)
    ; V
    [((.// U1 _) (.// U2 _)) (and (C≃ U1 U2))]
    [((.L i) (.L j)) (= i j)]
    ; U
    [((.Ar C1 V1 l^3) (.Ar C2 V2 l^3)) (C≃ V1 V2)]
    [((.St t V1*) (.St t V2*)) (andmap C≃ V1* V2*)]
    [((.λ↓ e1 ρ1) (.λ↓ e2 ρ2)) (and (C≃ e1 e2) (C≃ ρ1 ρ2))]
    [((.Λ/C C1 (.↓ e1 ρ1) v?) (.Λ/C C2 (.↓ e2 ρ2) v?))
     (and (= (length C1) (length C2)) (andmap C≃ C1 C2) (C≃ e1 e2) (C≃ ρ1 ρ2))]
    [((.St/C t C*) (.St/C t D*)) (andmap C≃ C* D*)]
    [((.μ/C x D1) (.μ/C x D2)) (C≃ D1 D2)]
    ; e
    [((.λ n e1) (.λ n e2)) (C≃ e1 e2)]
    [((.ref x m _) (.ref x m _)) #t]
    [((.@ f xs _) (.@ g ys _)) (and (C≃ f g) (andmap C≃ xs ys))]
    [((.@-havoc x) (.@-havoc y)) (equal? x y)]
    #;[((.apply f xs _) (.apply g ys _)) (and (C≃ f g) (C≃ xs ys))]
    [((.if i1 t1 e1) (.if i2 t2 e2)) (and (C≃ i1 i2) (C≃ t1 t2) (C≃ e1 e2))]
    [((.μ/c x c) (.μ/c x d)) (C≃ c d)]
    [((.->i xs y1 v?) (.->i zs y2 v?))
     (and (= (length xs) (length zs)) (andmap C≃ xs zs) (C≃ y1 y2))]
    [((.struct/c t cs) (.struct/c t ds)) (andmap C≃ cs ds)]
    ; ρ
    [((.ρ m1 l1) (.ρ m2 l2))
     (for/and ([i (in-range 0 (max l1 l2))])
       (match* ((hash-ref m1 (- l1 i 1) (λ () #f))
                (hash-ref m2 (- l2 i 1) (λ () #f)))
         [((? .V? V1) (? .V? V2)) (C≃ V1 V2)]
         [(x y) (equal? x y)]))]
    [(_ _) (equal? x y)]))
