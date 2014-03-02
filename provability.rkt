#lang typed/racket
(require "utils.rkt" "lang.rkt" "closure.rkt" #;"query-z3.rkt" "show.rkt" "query.rkt")
(provide (all-defined-out))

(:* [all-prove? all-refute? some-proves? some-refutes?] : .σ (Listof .V) .V → Bool)
(define (all-prove? σ V* C) (for/and ([V V*]) (match? (⊢ σ V C) 'Proved)))
(define (all-refute? σ V* C) (for/and ([V V*]) (match? (⊢ σ V C) 'Refuted)))
(define (some-proves? σ V* C) (for/or ([V V*]) (match? (⊢ σ V C) 'Proved)))
(define (some-refutes? σ V* C) (for/or ([V V*]) (match? (⊢ σ V C) 'Refuted)))

(: ⊢ : .σ .V .V → .R)
(define (⊢ σ V C)
  #;(printf "⊢:~nV:~a~nC:~a~n~n" V C #;(show-E σ V) #;(show-E σ C))
  (let ([C (simplify C)])
    (match (⊢′ σ V C)
      ['Neither (query σ V C)]
      [r #;(printf "Ans: ~a~n~n" r) r])))

; internal, lightweight, lo-tech prover
(: ⊢′ : (case→ [.σ .V .V → .R]
               [.σ .U .V → .R]
               [.σ .U .U → .R]))
(define (⊢′ σ V C)
  (define-set: assume : (Pairof (U .U .V) (U .U .V)) [assumed? assume!])
  
  ;; just for debugging
  (: show : .σ (U .V .U) → Any)
  (define (show σ x)
    (if (.V? x) (show-V σ x) (show-U σ x)))
  
  (: go : (case→ [.V .V → .R] [.U .V → .R] [.U .U → .R]))
  (define (go V C)
    (let: ([ans : .R
           (cond
      [(assumed? (cons V C)) 'Proved]
      [else
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
         [((and V (.μ/V x V*)) C)
          (assume! (cons V C))
          (let ([r (for/set: .R ([V (unroll V)]) (go V C))])
            (match (set-count r) ; TODO optimize?
              [0 'Proved]
              [1 (set-first r)]
              [_ (cond
                   [(for/and: : Bool ([ri r]) (equal? ri 'Proved)) 'Proved]
                   [(for/and: : Bool ([ri r]) (equal? ri 'Refuted)) 'Refuted]
                   [else 'Neither])]))]
         [((.X/V x) C) 'Proved]
         
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
               [(.o1) (decide-R (= n 1))]
               [(.o2) (decide-R (= n 2))]
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
               [(.o1) (decide-R (= n 1))]
               [(.o2) (decide-R (= n 2))]
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
            [(_ (and Uc (.μ/C x C′))) (assume! (cons V C)) (go U (unroll/C Uc))]
            
            ; conservative default
            [(_ _) 'Neither])])])])
      #;(printf "go:~nV: ~a~nC: ~a~nans: ~a~n~n" V C ans)
      ans))
  (go V C))

(: C*⇒C*? : (Setof .V) (Setof .V) → Bool)
(define (C*⇒C*? Cs Ds)
  (for/and ([D Ds]) (eq? 'Proved (C*⇒C Cs D))))

(: C*⇒C : (Setof .V) .V → .R)
(define (C*⇒C C* C)  
  (let: ([res : .R (match C
    [(.// (.St 'and/c (list C1 C2)) _) (∧R (C*⇒C C* C1) (C*⇒C C* C2))]
    [_ (for*/fold: ([R : .R 'Neither]) ([Ci C*])
         (match (C⇒C (simplify Ci) C) ; FIXME: can't use for/first with #:when
           ['Proved 'Proved]
           ['Refuted 'Refuted]
           ['Neither R]))])])
    #;(when (match? C (.// (? .Ar?) _))
      (printf "Here:~n~n~a~n~n~a~n~n~n" C* C)
      (printf "Res: ~a~n~n" res))
    res))

; checks whether first contract proves second
(: C⇒C : .V .V → .R)
(define (C⇒C C D)
  #;(printf "C:~n~a~nD:~n~a~n~n" C D)
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
            
            [(_ (.λ↓ (.λ 1 (.@ (or (.=) (.equal?)) (list (.x 0) (not (? .v?) (? .x?))) 'Λ) _) _)) 'Proved]
            
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

(: ⊑ : (case→ [.σ .σ → (case→
                        [.V .V → (Option .F)]
                        [(Listof .V) (Listof .V) → (Option .F)]
                        [.ρ .ρ → (Option .F)])]
              [.V .V → (Option .F)]
              [(Listof .V) (Listof .V) → (Option .F)]))
(define ⊑
  (match-lambda**
      [((? .σ? σ0) (? .σ? σ1))
       (define: F : .F (hash))
       (define-set: assume : (Pairof .V .V) (assumed? assume!))  
       
       (: go! : (case→ [.V .V → Bool]
                       [(Listof .V) (Listof .V) → Bool]
                       [.ρ .ρ → Bool]))
       (define (go! x y)
         #;(printf "go:~nσ0:~n~a~nσ1:~n~a~nV0:~n~a~nV1:~n~a~n~n" σ0 σ1 x y)
         (match* (x y)
           [((? .V? V0) (? .V? V1))
            (or        
             (assumed? (cons V0 V1))
             (match* (V0 V1)
               [((.// U0 C*) (.// U1 D*))
                (match* (U0 U1)
                  [((.•) (.•)) (C*⇒C*? C* D*)]
                  [((.St t V0*) (.St t V1*)) (andmap go! V0* V1*)]
                  [((.Ar C1 V1 _) (.Ar C2 V2 _)) (and (equal? C1 C2) (go! V1 V2))]
                  [((.λ↓ e0 ρ0) (.λ↓ e1 ρ1)) (and (equal? e0 e1) (go! ρ0 ρ1))]
                  [(_ (.•))
                   (match U0
                     [(.b (? int?)) (C*⇒C*? (set-add C* INT/C) D*)]
                     [(.b (? real?)) (C*⇒C*? (set-add C* REAL/C) D*)]
                     [(.b (? num?)) (C*⇒C*? (set-add C* NUM/C) D*)]
                     [(.b (? str?)) (C*⇒C*? (set-add C* STR/C) D*)]
                     [(.b (? sym?)) (C*⇒C*? (set-add C* SYM/C) D*)]
                     [_ (C*⇒C*? C* D*)])]
                  [(_ _) (equal? U0 U1)])]
               [((.L i) (.L j))
                (match (hash-ref F j #f)
                  [#f #;(printf "no key~n")
                      (if (go! (σ@ σ0 i) (σ@ σ1 j))
                          (begin #;(printf "lookedup yes~n")(set! F (hash-set F j i)) #t)
                          #f)]
                  [(? int? i′) #;(printf "yes key~n")(= i i′)])]
               [((.L i) _) (go! (σ@ σ0 i) V1)]
               [(_ (.L j)) (go! V0 (σ@ σ1 j))]
               [((? .μ/V? V0) (? .μ/V? V1))
                #;(printf "Case0: ~a~n~n~a~n~n" (show-V σ0 V0) (show-V σ1 V1))
                (assume! (cons V0 V1))
                (for/and: : Bool ([V0i (unroll V0)])
                  (for/or: : Bool ([V1i (unroll V1)]) ;FIXME: may screw up F
                    (let ([G F])
                      (or (go! V0i V1i) (begin (set! F G) #f)))))]
               [((? .μ/V? V0) _)
                #;(printf "Case2: ~a~n~n~a~n~n" (show-V σ0 V0) (show-V σ1 V1))
                (assume! (cons V0 V1))
                (for/and ([V0i (unroll V0)]) (go! V0i V1))]
               [(_ (? .μ/V? V1))
                #;(printf "Case1: ~a~n~n~a~n~n" (show-V σ0 V0) (show-V σ1 V1))
                (assume! (cons V0 V1))
                (for/or: : Bool ([V1i (unroll V1)])
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
    [((.@-havoc x) (.@-havoc y)) (equal? x y)]
    #;[((.apply f xs _) (.apply g ys _)) (and (C≃ f g) (C≃ xs ys))]
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