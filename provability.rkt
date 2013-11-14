#lang typed/racket
(require "utils.rkt" "lang.rkt" "closure.rkt" "query.rkt")
(provide (all-defined-out))

(:* [all-prove? all-refute? some-proves? some-refutes?] : .σ (Listof .V) .V → Bool)
(define (all-prove? σ V* C) (for/and ([V V*]) (match? (⊢′ σ V C) 'Proved)))
(define (all-refute? σ V* C) (for/and ([V V*]) (match? (⊢′ σ V C) 'Refuted)))
(define (some-proves? σ V* C) (for/or ([V V*]) (match? (⊢′ σ V C) 'Proved)))
(define (some-refutes? σ V* C) (for/or ([V V*]) (match? (⊢′ σ V C) 'Refuted)))

(: ⊢ : .σ .V .V → .R)
(define (⊢ σ V C)
  (let ([C (simplify C)])
    (match (⊢′ σ V C)
      ['Neither (query σ V C)]
      [r r])))

; internal, lightweight, lo-tech prover
(: ⊢′ : (case→ [.σ .V .V → .R]
               [.σ .U .V → .R]
               [.σ .U .U → .R]))
(define (⊢′ σ V C)
  (define: assume : (Setof (Pairof Sym .V)) ∅)
  
  (: assume! : Sym .V → Void)
  (define (assume! x y) (set! assume (set-add assume (cons x y))))
  (: assumed? : Sym .V → Bool)
  (define (assumed? x y) (set-member? assume (cons x y)))
  
  (: go : (case→ [.V .V → .R] [.U .V → .R] [.U .U → .R]))
  (define (go V C)
    (match* (V C)
      ; V ∈ C
      [((.L i) C)
       (match C ; HACK
         [(.// (.λ↓ (.λ 1 (.@ (or (.=) (.equal?)) (list-no-order (.x 0) (.x a)) _) #f) ρ) _)
          (match (ρ@ ρ (- (cast a Int) 1))
            [(.L j) (if (= i j) 'Proved (go (σ@ σ i) C))]
            [_ (go (σ@ σ i) C)])]
         [_ (go (σ@ σ i) C)])]
      [((.// U C*) C) (match (go U C)
                        ['Neither (C*⇒C C* C)]
                        [r r])]
      [((.μ/V x V*) C) (assume! x C)
                       (let ([r (for/set: .R ([V V*]) (go V C))])
                         (match (set-count r) ; TODO optimize?
                           [0 'Proved]
                           [1 (set-first r)]
                           [_ 'Neither]))]
      [((.X/V x) C) (if (assumed? x C) 'Proved 'Neither)]
      
      ; U ∈ C
      [((? .U? U) (? .V? C))
       (match C
         [(.L _) 'Neither]
         [(.// Uc _) (go U Uc)])]
      
      ; U ∈ U
      [(_ (.λ↓ (.λ _ (.b #t) _) _)) 'Proved] ; any
      [(_ (.λ↓ (.λ _ (.b #f) _) _)) 'Refuted] ; none
      [((.•) _) 'Neither] ; opaque, no further info
      [((? .U? U) (? .U? Uc))
       (match* (U Uc)
         ; negation
         [(_ (.St '¬/c (list C′))) (¬R (go U C′))]
         [(_ (.λ↓ (.λ n (.@ (.false?) (list e) l) v?) ρ)) (¬R (go U (.λ↓ (.λ n e v?) ρ)))]
         
         ; base predicates as contracts
         [([.b (? num?)] [.num?]) 'Proved]
         [([.b (? real?)] [.real?]) 'Proved]
         [([.b (? int?)] [.int?]) 'Proved]
         [([.b (? str?)] [.str?]) 'Proved]
         [([.b (? bool?)] [.bool?]) 'Proved]
         [([.b #t] [.true?]) 'Proved]
         [([.b #f] [.false?]) 'Proved]
         [([.b sym?] [.symbol?]) 'Proved]
         
         ; proc
         [((or (? .λ↓?) (? .Ar?) (? .o?)) (.proc?)) 'Proved]
         ; struct
         [((.St t _) (.st-p t _)) 'Proved]
         [((.St t V*) (.St/C t C*))
          (for/fold: ([r : .R 'Proved]) ([Vi V*] [Ci C*])
            (match r
              ['Refuted 'Refuted]
              [_ (match (go Vi Ci)
                   ['Proved r]
                   ['Refuted 'Refuted]
                   ['Neither 'Neither])]))]
         
         ; definite retutes for other concrete values
         [((not (? .λ↓?) (? .Ar?) (.o)) (.proc?)) 'Refuted]
         [(_ (? .St/C?)) 'Refuted]
         [(_ (? .pred?)) 'Refuted]
         
         ; special rules for reals. Had to split cases because TR doesn't play well with (or ...)
         [((.b b1) (.λ↓ (.λ 1 (.@ (or (.=) (.equal?))
                                  (or (list (.x 0) (.b b2)) (list (.b b2) (.x 0))) _) #f) _))
          (decide-R (equal? b1 b2))]
         [((.b (? real? r1)) (.λ↓ (.λ 1 (.@ (.≥) (list (.x 0) (.b (? real? r2))) _) #f) _))
          (decide-R (>= r1 r2))]
         [((.b (? real? r1)) (.λ↓ (.λ 1 (.@ (.≤) (list (.b (? real? r2)) (.x 0)) _) #f) _))
          (decide-R (>= r1 r2))]
         [((.b (? real? r1)) (.λ↓ (.λ 1 (.@ (.>) (list (.x 0) (.b (? real? r2))) _) #f) _))
          (decide-R (> r1 r2))]
         [((.b (? real? r1)) (.λ↓ (.λ 1 (.@ (.<) (list (.b (? real? r2)) (.x 0)) _) #f) _))
          (decide-R (> r1 r2))]
         [((.b (? real? r1)) (.λ↓ (.λ 1 (.@ (.≤) (list (.x 0) (.b (? real? r2))) _) #f) _))
          (decide-R (<= r1 r2))]
         [((.b (? real? r1)) (.λ↓ (.λ 1 (.@ (.≥) (list (.b (? real? r2)) (.x 0)) _) #f) _))
          (decide-R (<= r1 r2))]
         [((.b (? real? r1)) (.λ↓ (.λ 1 (.@ (.<) (list (.x 0) (.b (? real? r2))) _) #f) _))
          (decide-R (< r1 r2))]
         [((.b (? real? r1)) (.λ↓ (.λ 1 (.@ (.>) (list (.b (? real? r2)) (.x 0)) _) #f) _))
          (decide-R (< r1 r2))]
         
         ;; rules for arities
         ; arity includes
         [(_ (.λ↓ (.λ 1 (.@ (.arity-includes?) (list (.x 0) (.b (? int? n))) _) #f) _))
          (match U
            [(.λ↓ (.λ m _ v?) _) (if v? (decide-R (>= n (- m 1))) (decide-R (= m n)))]
            [(.Ar (.// (.Λ/C Cx _ v?) _) _ _)
             (if v? (decide-R (>= n (- (length Cx) 1))) (decide-R (= n (length Cx))))]
            [(or (? .st-p?) (? .st-ac?)) (decide-R (= n 1))]
            [(.st-mk _ m) (decide-R (= m n))]
            [_ 'Neither])]
         ; arity at least
         [(_ (.λ↓ (.λ 1 (.@ (.arity≥?) (list (.x 0) (.b (? int? n))) _) #f) _))
          (match U
            [(.λ↓ (.λ m _ v?) _) (if v? (decide-R (>= n (- m 1))) 'Refuted)]
            [(.Ar (.// (.Λ/C Cx _ v?) _) _ _) (if v? (decide-R (>= n (- (length Cx) 1))) 'Refuted)]
            [(.o) 'Refuted]
            [_ 'Neither])]
         ; arity exact
         [(_ (.λ↓ (.λ 1 (.@ (.arity=?) (list (.x 0) (.b (? int? n))) _) #f) _))
          (match U
            [(.λ↓ (.λ m _ v?) _) (if v? 'Refuted (decide-R (= m n)))]
            [(.Ar (.// (.Λ/C Cx _ v?) _) _ _) (if v? 'Refuted (decide-R (= (length Cx) n)))]
            [(or (? .st-p?) (? .st-ac?)) (decide-R (= n 1))]
            [(.st-mk _ m) (decide-R (= m n))]
            [_ 'Neither])]
         
         
         ; conjunctive, disjunctive, and recursive contracts
         [(_ (.St 'and/c (list P Q)))
          (match (go U P)
            ['Refuted 'Refuted]
            ['Proved (go U Q)]
            ['Neither (match (go U Q) ['Refuted 'Refuted] [_ 'Neither])])]
         [(_ (.St 'or/c (list P Q)))
          (match (go U P)
            ['Proved 'Proved]
            ['Refuted (go U Q)]
            ['Neither (match (go U Q) ['Proved 'Proved] [_ 'Neither])])]
         [(_ (and Uc (.μ/C x C′))) (go U (unroll/C Uc))]
         
         ; conservative default
         [(_ _) 'Neither])]))
  (go V C))

(: C*⇒C*? : (Setof .V) (Setof .V) → Bool)
(define (C*⇒C*? Cs Ds)
  (for/and ([D Ds]) (eq? 'Proved (C*⇒C Cs D))))

(: C*⇒C : (Setof .V) .V → .R)
(define (C*⇒C C* C)
  (for*/fold: ([R : .R 'Neither]) ([Ci C*])
    (match (C⇒C (simplify Ci) C) ; FIXME: can't use for/first with #:when
      ['Proved 'Proved]
      ['Refuted 'Refuted]
      ['Neither R])))

; checks whether first contract proves second
(: C⇒C : .V .V → .R)
(define (C⇒C C D)
  (let: go ([C C] [D D] [assume : (Setof (Pairof .V .V)) ∅])
    (cond
      [(C≃ C D) 'Proved]
      [(set-member? assume (cons C D)) 'Proved]
      [else
       (match* (C D)
         [((.// Uc _) (.// Ud _))
          (match* (Uc Ud)
            [(_ (.λ↓ (.λ _ (.b #t) _) _)) 'Proved] ; any
            [(_ (.λ↓ (.λ _ (.b #f) _) _)) 'Refuted] ; none
            [((? .pred? o1) (? .pred? o2)) (p⇒p o1 o2)] ; primitive predicates
            
            ; eliminate negation
            [((.St '¬/c (list C′)) (.St '¬/c (list D′)))
             (match (go D′ C′ assume) ['Proved 'Proved] [_ 'Neither])]
            [((.St '¬/c (list C′)) _) (match (go D C′ assume)
                                        ['Proved 'Refuted]
                                        [_ 'Neither])]
            [(_ (.St '¬/c (list D′))) (¬R (go C D′ assume))]
            
            ; special rules for reals
            [((.λ↓ (.λ 1 (.@ (.>) (list (.x 0) (.b (? real? r1))) _) _) _)
              (.λ↓ (.λ 1 (.@ (or (.>) (.≥)) (list (.x 0) (.b (? real? r2))) _) _) _))
             (if (>= r1 r2) 'Proved 'Neither)]
            [((.λ↓ (.λ 1 (.@ (.>) (list (.x 0) (.b (? real? r1))) _) _) _)
              (.λ↓ (.λ 1 (.@ (or (.=) (.<) (.≤)) (list (.x 0) (.b (? real? r2))) _) _) _))
             (if (>= r1 r2) 'Refuted 'Neither)]
            
            [((.λ↓ (.λ 1 (.@ (.≥) (list (.x 0) (.b (? real? r1))) _) _) _)
              (.λ↓ (.λ 1 (.@ (.>) (list (.x 0) (.b (? real? r2))) _) _) _))
             (if (> r1 r2) 'Proved 'Neither)]
            [((.λ↓ (.λ 1 (.@ (.≥) (list (.x 0) (.b (? real? r1))) _) _) _)
              (.λ↓ (.λ 1 (.@ (.≥) (list (.x 0) (.b (? real? r2))) _) _) _))
             (if (>= r1 r2) 'Proved 'Neither)]
            [((.λ↓ (.λ 1 (.@ (.≥) (list (.x 0) (.b (? real? r1))) _) _) _)
              (.λ↓ (.λ 1 (.@ (or (.≤) (.=)) (list (.x 0) (.b (? real? r2))) _) _) _))
             (if (> r1 r2) 'Refuted 'Neither)]
            [((.λ↓ (.λ 1 (.@ (.≥) (list (.x 0) (.b (? real? r1))) _) _) _)
              (.λ↓ (.λ 1 (.@ (.<) (list (.x 0) (.b (? real? r2))) _) _) _))
             (if (>= r1 r2) 'Refuted 'Neither)]
            
            [((.λ↓ (.λ 1 (.@ (.=) (list (.x 0) (.b (? real? r1))) _) _) _)
              (.λ↓ (.λ 1 (.@ o (list (.x 0) (.b (? real? r2))) _) _) _))
             (decide-R ((match o [(.=) =] [(.>) >] [(.<) <] [(.≥) >=] [(.≤) <=]) r1 r2))]
            
            [((.λ↓ (.λ 1 (.@ (.≤) (list (.x 0) (.b (? real? r1))) _) _) _)
              (.λ↓ (.λ 1 (.@ (.<) (list (.x 0) (.b (? real? r2))) _) _) _))
             (if (< r1 r2) 'Proved 'Neither)]
            [((.λ↓ (.λ 1 (.@ (.≤) (list (.x 0) (.b (? real? r1))) _) _) _)
              (.λ↓ (.λ 1 (.@ (.≤) (list (.x 0) (.b (? real? r2))) _) _) _))
             (if (<= r1 r2) 'Proved 'Neither)]
            [((.λ↓ (.λ 1 (.@ (.≤) (list (.x 0) (.b (? real? r1))) _) _) _)
              (.λ↓ (.λ 1 (.@ (or (.≥) (.=)) (list (.x 0) (.b (? real? r2))) _) _) _))
             (if (< r1 r2) 'Refuted 'Neither)]
            [((.λ↓ (.λ 1 (.@ (.≤) (list (.x 0) (.b (? real? r1))) _) _) _)
              (.λ↓ (.λ 1 (.@ (.>) (list (.x 0) (.b (? real? r2))) _) _) _))
             (if (<= r1 r2) 'Refuted 'Neither)]
            
            [((.λ↓ (.λ 1 (.@ (.<) (list (.x 0) (.b (? real? r1))) _) _) _)
              (.λ↓ (.λ 1 (.@ (or (.<) (.≤)) (list (.x 0) (.b (? real? r2))) _) _) _))
             (if (<= r1 r2) 'Proved 'Neither)]
            [((.λ↓ (.λ 1 (.@ (.<) (list (.x 0) (.b (? real? r1))) _) _) _)
              (.λ↓ (.λ 1 (.@ (or (.=) (.>) (.≥)) (list (.x 0) (.b (? real? r2))) _) _) _))
             (if (<= r1 r2) 'Refuted 'Neither)]
            
            ; struct
            [((.st-p t n) (.St/C t _)) (if (= n 0) 'Proved 'Neither)]
            [((.St/C t _) (.st-p t n)) (if (= n 0) 'Proved 'Neither)]
            [((.St/C t C*) (.St/C t D*))
             (for/fold: ([a : .R 'Proved]) ([Ci C*] [Di D*])
               (match a
                 ['Refuted 'Refuted]
                 [_ (match (go Ci Di assume) ['Proved a] [r r])]))]
            [((or (? .St/C?) (? .st-p?)) (or (? .pred?) (? .St/C?))) 'Refuted]
            [((.proc?) (or (? .St/C?) (? .st-p?) (? .pred?))) 'Refuted]
            
            ; recursive contracts
            [((.μ/C x C′) (.μ/C y D′)) (go (C/ C′ x C) (C/ D′ y D) (set-add assume (cons C D)))]
            [((.μ/C x C′) _) (go (C/ C′ x C) D (set-add assume (cons C D)))]
            [(_ (.μ/C y D′)) (go C (C/ D′ y D) (set-add assume (cons C D)))]
            
            ;; rules for arity
            ; arity exact
            [((.λ↓ (.λ 1 (.@ (.arity=?) (list (.x 0) (.b (? int? m))) _) #f) _)
              (.λ↓ (.λ 1 (.@ (.arity=?) (list (.x 0) (.b (? int? n))) _) #f) _))
             (decide-R (= m n))]
            [((.λ↓ (.λ 1 (.@ (.arity≥?) (list (.x 0) (.b (? int? m))) _) #f) _)
              (.λ↓ (.λ 1 (.@ (.arity=?) (list (.x 0) (.b (? int? n))) _) #f) _))
             'Refuted]
            [((.λ↓ (.λ 1 (.@ (.arity-includes?) (list (.x 0) (.b (? int? m))) _) #f) _)
              (.λ↓ (.λ 1 (.@ (.arity=?) (list (.x 0) (.b (? int? n))) _) #f) _))
             (if (= m n) 'Neither 'Refuted)]
            ; arity at least
            [((.λ↓ (.λ 1 (.@ (.arity=?) (list (.x 0) (.b (? int? m))) _) #f) _)
              (.λ↓ (.λ 1 (.@ (.arity≥?) (list (.x 0) (.b (? int? n))) _) #f) _))
             'Refuted]
            [((.λ↓ (.λ 1 (.@ (.arity≥?) (list (.x 0) (.b (? int? m))) _) #f) _)
              (.λ↓ (.λ 1 (.@ (.arity≥?) (list (.x 0) (.b (? int? n))) _) #f) _))
             (if (>= m n) 'Proved 'Neither)]
            [((.λ↓ (.λ 1 (.@ (.arity-includes?) (list (.x 0) (.b (? int? m))) _) #f) _)
              (.λ↓ (.λ 1 (.@ (.arity≥?) (list (.x 0) (.b (? int? n))) _) #f) _))
             'Neither]
            ; arity includes
            [((.λ↓ (.λ 1 (.@ (.arity=?) (list (.x 0) (.b (? int? m))) _) #f) _)
              (.λ↓ (.λ 1 (.@ (.arity-includes?) (list (.x 0) (.b (? int? n))) _) #f) _))
             (decide-R (= m n))]
            [((.λ↓ (.λ 1 (.@ (.arity≥?) (list (.x 0) (.b (? int? m))) _) #f) _)
              (.λ↓ (.λ 1 (.@ (.arity-includes?) (list (.x 0) (.b (? int? n))) _) #f) _))
             (if (>= n m) 'Proved 'Neither)]
            [((.λ↓ (.λ 1 (.@ (.arity-includes?) (list (.x 0) (.b (? int? m))) _) #f) _)
              (.λ↓ (.λ 1 (.@ (.arity-includes?) (list (.x 0) (.b (? int? n))) _) #f) _))
             (if (= m n) 'Proved 'Neither)]
            
            ; break apart composit contracts
            [((.St 'or/c (list C1 C2)) _)
             (match* ((go C1 D assume) (go C2 D assume))
               [('Proved 'Proved) 'Proved]
               [('Refuted 'Refuted) 'Refuted]
               [(_ _) 'Neither])]
            [(_ (.St 'and/c (list D1 D2))) (∧R (go C D1 assume) (go C D2 assume))]
            [(_ (.St 'or/c (list D1 D2))) (∨R (go C D1 assume) (go C D2 assume))]
            [((.St 'and/c (list C1 C2)) _)
             (match* ((go C1 D assume) (go C2 D assume))
               [('Proved _) 'Proved]
               [(_ 'Proved) 'Proved]
               [('Refuted 'Refuted) 'Refuted]
               [(_ _) 'Neither])]
            [(_ _) 'Neither])] ; default
         [(_ _) 'Neither])]))) ; default

(: p⇒p : .pred .pred → .R)
(define (p⇒p p q)
  (cond
    [(equal? p q) 'Proved]
    [else
     (match* (p q)
       [((or (.true?) (.false?)) (.bool?)) 'Proved]
       [((or (.real?) (.int?)) (.num?)) 'Proved]
       [((.int?) (.real?)) 'Proved]
       [((.bool?) (or (.true?) (.false?))) 'Neither]
       [((.num?) (or (.real?) (.int?))) 'Neither]
       [((.real?) (.int?)) 'Neither]
       [((.st-p t _) (.st-p t _)) 'Proved]
       [(_ _) 'Refuted])]))

(: ¬R : .R → .R)
(define ¬R
  (match-lambda ['Proved 'Refuted] ['Refuted 'Proved] [_ 'Neither]))

(define-syntax ∨R
  (syntax-rules ()
    [(_ e) e]
    [(_ e1 e ...) (match e1
                    ['Proved 'Proved]
                    ['Refuted (∨R e ...)]
                    ['Neither (match (∨R e ...) ['Proved 'Proved] [_ 'Neither])])]))

(define-syntax ∧R
  (syntax-rules ()
    [(_ e) e]
    [(_ e1 e ...) (match e1
                    ['Proved (∧R e ...)]
                    ['Refuted 'Refuted]
                    ['Neither (match (∧R e ...) ['Refuted 'Refuted] [_ 'Neither])])]))
(: decide-R : Bool → .R)
(define decide-R (match-lambda [#t 'Proved] [#f 'Refuted]))

(: ⊑ : .V .V → Bool)
(define (⊑ V0 V1)
  (match* (V0 V1)
    [((.// (.•) C*) (.// (.•) D*)) (C*⇒C*? C* D*)]
    [((.// U _) (.// U _)) #t]
    [((.// U C*) (.// (.•) D*))
     (match U
       [(.b (? real?)) (C*⇒C*? (set-add C* (Prim 'real?)) D*)]
       [(.b (? int?)) (C*⇒C*? (set-add C* (Prim 'int?)) D*)]
       [(.b (? num?)) (C*⇒C*? (set-add C* (Prim 'num?)) D*)]
       [(.b (? str?)) (C*⇒C*? (set-add C* (Prim 'str?)) D*)]
       [(.b (? sym?)) (C*⇒C*? (set-add C* (Prim 'symbol?)) D*)]
       [(.St t V*) (C*⇒C*? (set-add C* (→V (.st-p t (length V*)))) D*)]
       [(.Ar (.// (.Λ/C Cx _ v?) _) V _)
        (C*⇒C*? (set-add (set-add C* (Prim 'proc?))
                         (if v? (arity≥/C (- (length Cx) 1)) (arity=/C (length Cx))))
                D*)]
       [(.λ↓ (.λ n _ v?) _) (C*⇒C*? (set-add (set-add C* (Prim 'proc?))
                                             (if v? (arity≥/C (- n 1)) (arity=/C n)))
                                    D*)]
       [_ (C*⇒C*? C* D*)])]
    [((.// (.•) C*) (.// (.•) D*)) (C*⇒C*? C* D*)]
    [((.μ/V 'x V0*) (.μ/V 'z V1*)) (for/and ([V0 V0*]) (for/or: : Bool ([V1 V1*]) (⊑ V0 V1)))]
    [((.X/V _) (.X/V _)) #t]
    [(_ _) #f]))

(: C≃ : (case→ [.V .V → Bool]
              [.U .U → Bool]
              [.e .e → Bool]
              [.ρ .ρ → Bool]))
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
    [((.λ n e1 v?) (.λ n e2 v?)) (C≃ e1 e2)]
    [((.ref x m _) (.ref x m _)) #t]
    [((.@ f xs _) (.@ g ys _)) (and (C≃ f g) (andmap C≃ xs ys))]
    [((.if i1 t1 e1) (.if i2 t2 e2)) (and (C≃ i1 i2) (C≃ t1 t2) (C≃ e1 e2))]
    [((.μ/c x c) (.μ/c x d)) (C≃ c d)]
    [((.λ/c xs y1 v?) (.λ/c zs y2 v?))
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