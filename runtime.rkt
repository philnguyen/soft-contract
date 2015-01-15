#lang typed/racket/base
(require racket/match racket/list racket/set
         "utils.rkt" "lang.rkt")
(require/typed redex/reduction-semantics [variable-not-in (Any Symbol → Symbol)])
(provide (all-defined-out))

(define m∅ : (Map (U Integer Symbol) .V) (hash))
(define-type .R (U 'Proved 'Refuted 'Neither))

;;;;; CLOSURE

;; closure forms
(define-data .E
  (struct .↓ [e : .expr] [ρ : .ρ])
  (struct .FC [c : .V] [v : .V] [ctx : Any])
  (struct .Mon [c : .E] [e : .E] [l³ : Id³])
  (struct .Assume [v : .V] [c : .V])
  (subset: .A
    (struct .blm [violator : Symbol] [origin : Symbol] [v : .V] [c : .V])
    (subset: .V ; either label or refined prevalue
      (struct .L [i : Integer])
      (struct .// [pre : .U] [refine : (Setof .V)])
      ;; The counterexample engine does not use these
      (struct .μ/V [x : Symbol] [Vs : (Setof .V)])
      (struct .X/V [x : Symbol]))))

(define-type .V+ (U .// .μ/V))

;; blessed arrow, struct, and closed lambda
(define-data .U
  .prim
  '•
  (struct .Ar [c : .V] [v : .V] [l^3 : Symbol^3])
  (struct .St [tag : Identifier] [fields : (Listof .V)])
  (struct .λ↓ [f : .λ] [ρ : .ρ])
  (struct .Λ/C [c : (Listof .V)] [d : .↓] [v? : Boolean])
  (struct .St/C [t : Identifier] [fields : (Listof .V)])
  (struct .μ/C [x : Symbol] [c : .V])
  (struct .X/C [x : Symbol])
  (struct .Case [m : (Map (Listof .V) .L)]))

(define Case∅ (.Case (hash)))

(: .Case@ : .Case (Listof .V) → (Option .L))
(define (.Case@ c xs)
  (match-define (.Case m) c)
  (hash-ref m xs #f))

(: .Case+ : .Case (Listof .V) .L → .Case)
(define (.Case+ c xs y)
  (match-define (.Case m) c)
  (.Case (hash-set m xs y)))

(: .¬/C : .V → .V)
(define (.¬/C V) (.// (.St '¬/c (list V)) ∅))

; evaluation answer. New type instead of cons to work well with pattern matching
(define-type .Ans (Pairof .σ .A))
(define-type .Ans+ (Setof .Ans))
(define-type .Ans* (U .Ans .Ans+))
(define-type .Vns (Pairof .σ .V))
(define-type .Vns* (U .Vns (Setof .Vns)))

(: close : .v .ρ → .V)
(define (close v ρ)
  #;(printf "close:~n~a~n~a~n" v ρ)
  (match v ; partial
    [(? .#%plain-lambda? v) (→V (.λ↓ v (restrict ρ (FV v))))]
    [(? .prim? p) (→V p)]))

(: →V : .U → .//)
(define (→V U) (.// U ∅))

;; maps abstract to concrete labels
(define-type .F (Map Integer Integer))
(define F∅ : .F (hash))
(define .F? hash?)


;;;;; REUSED CONSTANTS

(: Prim : (U Symbol Number String Boolean) → .//)
(define Prim
  (memoize
   #:eq? #t
   (match-lambda
     [(or 'mt 'empty) MT]
     [(and (or (? symbol?) (? number?) (? string?) #t #f) name)
      (match (prim name)
        [(? .prim? b) (.// b ∅)]
        [(? .λ? f) (.// (.λ↓ f ρ∅) ∅)]
        [#f (error 'Prim "Unknown primitive name `~a`" name)])])))

(define** 
  [MT (→V (.St 'empty empty))]
  [♦ (→V '•)] [V∅ (.μ/V '_ ∅)]
  [ZERO (Prim 0)] [ONE (Prim 1)] [TT (Prim #t)] [FF (Prim #f)]
  [INT/C (Prim 'integer?)] [REAL/C (Prim 'real?)] [NUM/C (Prim 'number?)]
  [STR/C (Prim 'string?)] [PROC/C (Prim 'procedure?)] [SYM/C (Prim 'symbol?)])


;;;;; ENVIRONMENT

;; environment maps static distances (HACK: or symbols) to values
(struct .ρ ([map : (Map (U Integer Symbol) .V)] [len : Integer]) #:transparent) ; FIXME equality
(define ρ∅ (.ρ m∅ 0))

(: restrict : .ρ (Setof Integer) → .ρ)
(define (restrict ρ sd*)
  (cond
   [(set-empty? sd*) ρ∅]
   [else
    (match-define (.ρ m l) ρ)
    (define m′
      (for/fold ([acc : (Map (U Integer Symbol) .V) m∅]) ([sd sd*])
        (define i (- l sd 1))
        (hash-set acc i (hash-ref m i))))
    (.ρ m′ l)]))

(: ρ+ : (case→ [.ρ .V → .ρ]
               [.ρ Symbol .V → .ρ]))
(define ρ+
  (match-lambda*
    [(list (.ρ m l) (? .V? V)) (.ρ (hash-set m l V) (+ 1 l))]
    [(list (.ρ m l) (? symbol? x) (? .V? V)) (.ρ (hash-set m x V) l)]))

(: ρ++ (case→ [.ρ (Listof .V) → .ρ]
              [.ρ (Listof .V) (U Boolean Integer) → .ρ]))
(define (ρ++ ρ V* [var? #f])
  (match var?
    [#f (for/fold ([ρi ρ]) ([V V*]) (ρ+ ρi V))]
    [0 (ρ+ ρ (foldr (λ: ([Vi : .V] [Vr : .V])
                      (.// (.St 'cons (list Vi Vr)) ∅))
                    MT V*))]
    [(? integer? n) (ρ++ (ρ+ ρ (car V*)) (cdr V*) (- n 1))]))

(: ρ@ : .ρ (U .x Integer .x/c Symbol) → .V)
(define (ρ@ ρ x)
  (match-let ([(.ρ m l) ρ])
    (hash-ref m (match x
                  [(.x sd) (- l sd 1)]
                  [(? integer? sd) (- l sd 1)]
                  [(.x/c x) x]
                  [(? symbol? x) x]))))

(: ρ-set : .ρ (U .x Integer) .V → .ρ)
(define (ρ-set ρ x V)
  (match-let ([(.ρ m l) ρ]
              [sd (match x [(.x sd) sd] [(? integer? sd) sd])])
    (.ρ (hash-set m (- l sd 1) V) l)))

(: ρ∋ : .ρ (U .x Integer) → Boolean)
(define (ρ∋ ρ x)
  (match-let ([(.ρ m l) ρ]
              [sd (match x [(.x sd) sd] [(? integer? sd) sd])])
    (hash-has-key? m (- l sd 1))))

;;;;; STORE

;; store maps label indices to refined prevalues
(struct: .σ ([map : (Map Integer .V+)] [next : Integer]) #:transparent)
(define σ∅ (.σ (hash) 0))

(: σ@ : (case→ [.σ (U .L Integer) → .V+]
               [.σ .// → .//]
               [.σ .μ/V → .μ/V]
               [.σ .X/V → .X/V]
               [.σ .V → .V]))
(define (σ@ σ a)
  (match a
    [(.L i) (hash-ref (.σ-map σ) i)]
    [(? integer? i) (hash-ref (.σ-map σ) i)]
    [(and (? .V? V) (not (? .L?))) V]))

; allocates new location with given refinements.
; does NOT handle redundant/bogus refinements.
(: σ+ : .σ (U .V (Setof .V) #f) * → (Values .σ .L))
(define (σ+ σ . C*)
  (match-define (.σ m i) σ)
  (define Cs
    (for/fold ([a : (Setof .V) ∅]) ([C C*])
      (match C
        [(? set? s) (set-union a s)]
        [(? .V? C) (when (match? C (.// '• _)) (error "ha!")) (set-add a C)]
        [_ a])))
  (values (.σ (hash-set m i (if (set-empty? Cs) ♦ (.// '• Cs))) (+ 1 i))
          (.L i)))

(: σ++ : .σ Integer → (Values .σ (Listof .L)))
(define (σ++ σ n)
  (match-define (.σ m lo) σ)
  (define hi (+ lo n))
  (define r (range lo hi))
  (values (.σ (for/fold ([m m]) ([i r]) (hash-set m i ♦)) hi)
          (map .L r)))

(define-syntax σ-set
  (syntax-rules ()
    [(_ σ) σ]
    [(_ σ k v rest ...) (σ-set (σ-set₁ σ k v) rest ...)]))

(: σ-set₁ : .σ (U .L Integer) .V+ → .σ)
(define (σ-set₁ σ a V)
  (match-let ([(.σ m l) σ]
              [i (match a [(.L i) i] [(? integer? i) i])])
    (.σ (hash-set m i V) l)))

; substitute contract for given symbol
(: C/ : .V Symbol .V → .V)
(define (C/ V x V′)
  (match V
    [(.L _) V]
    [(.// U D*)
     (match U
       [(.X/C z) (if (eq? x z) V′ V)]
       [(.Ar C V l^3) (.// (.Ar (C/ C x V′) (C/ V x V′) l^3) D*)]
       [(.St t V*) (.// (.St t (for/list ([Vi V*]) (C/ Vi x V′))) D*)]
       [(.λ↓ f ρ) (.// (.λ↓ f (ρ+ ρ x V′)) D*)]
       [(.Λ/C C* (.↓ d ρ) v?)
        (.// (.Λ/C (for/list ([C C*]) (C/ C x V′)) (.↓ d (ρ+ ρ x V′)) v?) D*)]
       [(.St/C t C*) (.// (.St/C t (for/list ([C C*]) (C/ C x V′))) D*)]
       [(.μ/C z C) (.// (if (eq? z x) U (.μ/C z (C/ C x V′))) D*)]
       [(? .prim? p) V])]))

;; if only one argument is present, (→C o V2) means λx.(o x V2)
;; if both are present, (→C o V1 V2) means λx.(= x (o V1 V2))
(: →C : .o [#:1st (U #f .V)] [#:2nd (U #f .V)] → .V)
(define (→C o #:1st [V1 #f] #:2nd [V2 #f])
  (match* (V1 V2)
    [((? .V? V1) #f)
     (→V (match V1
           [(.// (? .b? b) _) (.λ↓ (.λ 1 (.@ o (list b (.x 0)) 'Λ) #f) ρ∅)]
           [_ (.λ↓ (.λ 1 (.@ o (list (.x 1) (.x 0)) 'Λ) #f) (ρ+ ρ∅ V1))]))]
    [(#f (? .V? V2))
     (→V (match V2
           [(.// (? .b? b) _) (.λ↓ (.λ 1 (.@ o (list (.x 0) b) 'Λ) #f) ρ∅)]
           [_ (.λ↓ (.λ 1 (.@ o (list (.x 0) (.x 1)) 'Λ) #f) (ρ+ ρ∅ V2))]))]
    [((? .V? V1) (? .V? V2))
     (→V (match* (V1 V2)
           [((.// (? .b? c) _) (.// (? .b? d) _))
            (.λ↓ (.λ 1 (.@ '= (list (.x 0) (.@ o (list c d) 'Λ)) 'Λ) #f) ρ∅)]
           [((.// (? .b? c) _) _)
            (.λ↓ (.λ 1 (.@ '= (list (.x 0) (.@ o (list c (.x 1)) 'Λ)) 'Λ) #f) (ρ+ ρ∅ V2))]
           [(_ (.// (? .b? d) _))
            (.λ↓ (.λ 1 (.@ '= (list (.x 0) (.@ o (list (.x 1) d) 'Λ)) 'Λ) #f) (ρ+ ρ∅ V1))]
           [(_ _)
            (.λ↓ (.λ 1 (.@ '= (list (.x 0) (.@ o (list (.x 2) (.x 1)) 'Λ)) 'Λ) #f) (ρ++ ρ∅ (list V1 V2)))]))]))


(define**
  [ZERO/C (→C '= #:2nd ZERO)]
  [POS/C (→C '> #:2nd ZERO)]
  [NEG/C (→C '< #:2nd ZERO)]
  [NON-NEG/C (→C '>= #:2nd ZERO)]
  [NON-POS/C (→C '<= #:2nd ZERO)]
  [ONE/C (→C '= #:2nd ONE)])
(define NON-ZERO/C (.¬/C ZERO/C))
(: sign/C : Real → (Setof .V))
(define (sign/C x) ; TODO ridiculous, yea...
  (cond [(> x 0) {set POS/C NON-NEG/C NON-ZERO/C}]
        [(= x 0) {set ZERO/C NON-NEG/C NON-POS/C}]
        [else {set NEG/C NON-ZERO/C NON-POS/C}]))

(:* [+/C -/C */C ÷/C] : .V .V → .V)
(define (+/C V1 V2) (→C '+ #:1st V1 #:2nd V2))
(define (-/C V1 V2) (→C '- #:1st V1 #:2nd V2))
(define (*/C V1 V2) (→C '* #:1st V1 #:2nd V2))
(define (÷/C V1 V2) (→C '/ #:1st V1 #:2nd V2))

(: sqrt/C : .V → .V)
(define (sqrt/C V)
  (→V
   (match V
     [(.// (? .b? b) _) (.λ↓ (.λ 1 (.@ '= (list (.x 0) (.@ 'sqrt (list b) 'Λ)) 'Λ) #f) ρ∅)]
     [_ (.λ↓ (.λ 1 (.@ '= (list (.x 0) (.@ 'sqrt (list (.x 1)) 'Λ)) 'Λ) #f) (ρ+ ρ∅ V))])))
 
(:* [</C >/C ≥/C ≤/C =/C ≠/C string-length/C] : .V → .V)
(define (</C V) (→C '< #:2nd V))
(define (>/C V) (→C '> #:2nd V))
(define (≥/C V) (→C '>= #:2nd V))
(define (≤/C V) (→C '<= #:2nd V))
(define (=/C V) (→C '= #:2nd V))
(define (≠/C V) (.¬/C (=/C V)))
(define (string-length/C V) (→C 'string-length #:2nd V))

(:* [arity=/C arity≥/C arity-includes/C] : Integer → .V)
(define (arity=/C n) (→C 'arity=? #:2nd (Prim n)))
(define (arity≥/C n) (→C 'arity>=? #:2nd (Prim n)))
(define (arity-includes/C n) (→C 'arity-includes? #:2nd (Prim n)))

;; simplifies predicate
(: simplify : .V → .V)
(define (simplify V)
  (match V
    [(.L _) V]
    [(.// U C*)
     (match U
       [(.λ↓ f ρ)
        ; η-simplify
        (match f
          [(.λ 1 (.@ (.x i) (list (.x 0)) _) #f) (simplify (ρ@ ρ (- i 1)))]
          [(.λ 1 (.@ (? .v? v) (list (.x 0)) _) #f)
           (match v
             [(? .•ₗ?) ♦]
             [(? .prim? p) (→V p)]
             [(and (? .λ? f) (? closed? f)) (simplify (.// (.λ↓ f ρ∅) C*))]
             [_ V])]
          [(.λ 1 (.@ '= (list (.x 0) (.@ 'add1 (list e) l)) g) #f)
           (.// (.λ↓ (.λ 1 (.@ '= (list (.x 0) (.@ '+ (list e .one) l)) g) #f) ρ) C*)]
          [(.λ 1 (.@ '= (list (.x 0) (.@ 'sub1 (list e) l)) g) #f)
           (.// (.λ↓ (.λ 1 (.@ '= (list (.x 0) (.@ '- (list e .one) l)) g) #f) ρ) C*)]
          [_ V])]
       [(.Ar (.// (.Λ/C (list (.// (.λ↓ (.λ 1 (.b #t) _) _) _)) (.↓ 'boolean? _) _) _)
             (and p (.// (or (? .pred?) (? .st-p?)) _)) _)
        p]
       [(.Ar (.// (.Λ/C (list (.// (.λ↓ (.λ 1 (.b #t) _) _) _) ...) (.↓ (.λ 1 (.b #t) _) _) _) _)
             V _)
        (simplify V)]
       [_ V])]
    [_ V]))

(: unroll/C : .μ/C → .V)
(define (unroll/C U) (match-let ([(.μ/C x C′) U]) (C/ C′ x (→V U))))

(: flat/C? : .σ (U .U .V) → Boolean)
(define (flat/C? σ V) ; returns whether value is definitely a flat contract
  (let go ([V V])
    (match V
      [(.L i) (go (σ@ σ i))]
      [(.// U _) (go U)]
      [(.St/C _ C*) (andmap go C*)]
      [(.St _ C*) (andmap go C*)]      
      [(.μ/C _ D) (go D)]
      [(? .Λ/C?) #f]
      [_ #t])))

;; return all sub-values as lambdas with similar function body
(: repeated-lambdas : .λ .ρ → (Setof .V))
(define (repeated-lambdas e ρ)
  (define-set ac : .V)
  (: go! : (U .V .ρ) → Void)
  (define go!
    (match-lambda
      [(and V (.// (.λ↓ f ρ1) _)) (if (equal? f e) (ac-add! V) (go! ρ1))]
      [(.// (.Ar _ V′ _) _) (go! V′)]
      [(.ρ m _) (for ([V (in-hash-values m)]) (go! V))]
      [_ (void)]))
  (go! ρ)
  ac)

(: mk-box : .V → .//)
(define (mk-box V) (→V (.St 'box (list V))))

(: subst/L : (case->
              [.L .F → .L]
              [.// .F → .//]
              [.μ/V .F → .μ/V]
              [(U .// .μ/V) .F → (U .// .μ/V)]
              [.V .F → .V]
              [(Setof .V) .F → (Setof .V)]))
(define (subst/L V F)
  (: go/V : (case->
             [.L → .L]
             [.// → .//]
             [.μ/V → .μ/V]
             [.V+ → .V+]
             [.V → .V]))
  (define go/V
    (match-lambda
     [(and V (.L i))
      (match (hash-ref F i #f)
        [(? integer? j) (.L j)]
        [_ V])]
     [(.// U C*) (.// (go/U U) (for/set: .V ([Ci C*]) (go/V Ci)))]
     [(.μ/V x V*) (.μ/V x (for/set: .V ([Vi V*]) (go/V Vi)))]
     [(? .X/V? V) V]))
  
  (: go/U : .U → .U)
  (define go/U
    (match-lambda
     [(.Ar C V l) (.Ar (go/V C) (go/V V) l)]
     [(.St t V*) (.St t (go/V* V*))]
     [(.λ↓ f ρ) (.λ↓ f (go/ρ ρ))]
     [(.Λ/C Cx (.↓ e ρ) v?) (.Λ/C (go/V* Cx) (.↓ e (go/ρ ρ)) v?)]
     [(.St/C t V*) (.St/C t (go/V* V*))]
     [(.μ/C x C) (.μ/C x (go/V C))]
     [U U]))
  
  (: go/ρ : .ρ → .ρ)
  (define (go/ρ ρ)
    (match-define (.ρ m l) ρ)
    (.ρ ;; TODO: either wrong or dumb, rewrite using for/hash
     (for/fold ([acc : (Map (U Symbol Integer) .V) m]) ([k (in-hash-keys m)])
       (match (hash-ref m k #f)
         [(? .V? V) (hash-set acc k (go/V V))]
         [_ acc]))
     l))
  
  (: go/V* : (Listof .V) → (Listof .V))
  (define (go/V* V*) (map go/V V*))
  
  (: go/Vs : (Setof .V) → (Setof .V))
  (define (go/Vs Vs)
    (for/set: .V ([V (in-set Vs)]) (go/V V)))

  (cond [(set? V) (go/Vs V)]
        [else (go/V V)]))

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
                [(? integer? j) (.L j)]
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
      [(and U (or (? .X/C?) (? .prim?) '•)) U]
      ;ρ
      [(.ρ m l)
       (.ρ
        (for/fold : (Map (U Symbol Integer) .V) ([acc : (Map (U Symbol Integer) .V) m]) ([k (in-hash-keys m)])
          (match (hash-ref m k #f)
            [#f acc]
            [(? .V? V) (hash-set acc k (go! V))]))
        l)]
      ; List
      [(? list? V*) (map go! V*)]))
  
  (: transfer? : .V → Boolean)
  (define (transfer? C)
    (match C
      [(.L i) (hash-has-key? F i)]
      [(.// U _) (match U
                   [(? .prim?) #t]
                   ['• #f]
                   [(.Ar C V _) (and (transfer? C) (transfer? V))]
                   [(.St _ V*) (andmap transfer? V*)]
                   [(.λ↓ f (.ρ m _)) (for/and : Boolean ([V (in-hash-values m)])
                                       (transfer? V))]
                   [(.Λ/C C (.ρ m _) _)
                    (and (andmap transfer? C)
                         (for/and : Boolean ([V (in-hash-values m)])
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
  
  (define V-new (go! V-old))
  #;(unless (well-formed? σ-new V-new)
  (error "malformed"))
  (list σ-new V-new F))

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
                          #;(match? C (.// (.λ↓ (.λ 1 (.@ '= (list (.x 0) _) 'Λ) #f) _) _)))
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
(: V∈ : .V .V → Boolean)
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
       (let ([m′ (for/fold ([m′ : (Map (U Integer Symbol) .V) m∅]) ([x (in-hash-keys m)])
                   (hash-set m′ x (go (hash-ref m x))))])
         (if (equal? m′ m) ρ (.ρ m′ l)))]))
  (match V0
    [(? set? s) (for/set: .V ([x s]) (go x))]
    [(? list? l) (map go l)]
    [(? .V? V) (go V)]
    [(? .ρ? ρ) (go ρ)]))

; generates a symbol not appearing in value (for μ/V x {...})
(: fresh : (U .V (Setof .V) (Listof .V)) → Symbol)
(define (fresh V)
  
  (: col : (U .V (Setof .V) (Listof .V)) → (Setof Symbol))
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
      [(? set? V*) (for/fold ([s : (Setof Symbol) ∅]) ([V V*])
                     (set-union s (col V)))]
      [(? list? V*) (for/fold ([s : (Setof Symbol) ∅]) ([V V*])
                      (set-union s (col V)))]))
  
  (variable-not-in (set->list (col V)) 'X))
