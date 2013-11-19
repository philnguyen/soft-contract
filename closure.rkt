#lang typed/racket
(require "utils.rkt" "lang.rkt")
(require/typed redex [variable-not-in (Any Sym → Sym)])
(provide (all-defined-out))

(define: m∅ : (Map (U Int Sym) .V) (hash))
(define-type .R (U 'Proved 'Refuted 'Neither))

;;;;; CLOSURE

;; closure forms
(define-data (.E)
  (.↓ [e : .e] [ρ : .ρ])
  (.FC [c : .V] [v : .V] [ctx : Sym])
  (.Mon [c : .E] [e : .E] [l^3 : Sym^3])
  (.Assume [v : .V] [c : .V])
  (subset: (.A)
    (subset: (.blm [violator : Sym] [origin : Sym] [v : .V] [c : .V]))
    (subset: (.V) ; either label or refined prevalue
      (.L [i : Int])
      (.// [pre : .U] [refine : (Setof .V)])
      (.μ/V [x : Sym] [Vs : (Setof .V)])
      (.X/V [x : Sym]))))

;; blessed arrow, struct, and closed lambda
(define-type .U (U .prim .• .Ar .St .λ↓ .Λ/C .St/C .μ/C .X/C))
(define-predicate .U? .U)
(struct: .Ar ([c : .V] [v : .V] [l^3 : Sym^3]) #:transparent)
(struct: .St ([tag : Sym] [fields : (Listof .V)]) #:transparent)
(struct: .λ↓ ([f : .λ] [ρ : .ρ]) #:transparent)
(struct: .Λ/C ([c : (Listof .V)] [d : .↓] [v? : Bool]) #:transparent)
(struct: .St/C ([t : Sym] [fields : (Listof .V)]) #:transparent)
(struct: .μ/C ([x : Sym] [c : .V]) #:transparent)
(struct: .X/C ([x : Sym]) #:transparent)

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
  (match v ; partial
    [(? .λ? v) (→V (.λ↓ v (restrict ρ (FV v))))]
    [(? .prim? p) (→V p)]))

(: →V : (case→ [.U → .//]))
(define (→V U) (.// U ∅))

(define-type .F (Setof (Pairof .L .L)))

;;;;; REUSED CONSTANTS

(: Prim : (U Sym Num String Bool) → .V)
(define Prim
  (memoize
   #:eq? #t
   (match-lambda
     ['mt MT]
     [(and (or (? sym?) (? num?) (? str?) #t #f) name)
      (match (prim name)
        [(? .prim? b) (.// b ∅)]
        [(? .λ? f) (.// (.λ↓ f ρ∅) ∅)]
        [#f (error "Prim: " name)])])))

(define** 
  [MT (→V (.St 'empty empty))]
  [♦ (→V •)] [V∅ (.μ/V '_ ∅)]
  [ZERO (Prim 0)] [ONE (Prim 1)] [TT (Prim #t)] [FF (Prim #f)]
  [INT/C (Prim 'int?)] [REAL/C (Prim 'real?)] [NUM/C (Prim 'num?)]
  [STR/C (Prim 'str?)] [PROC/C (Prim 'proc?)])

;;;;; ENVIRONMENT

;; environment maps static distances (HACK: or symbols) to values
(struct: .ρ ([map : (Map (U Int Sym) .V)] [len : Int]) #:transparent) ; FIXME equality
(define ρ∅ (.ρ m∅ 0))

(: restrict : .ρ (Setof Int) → .ρ)
(define (restrict ρ sd*)
  (if (set-empty? sd*) ρ∅ ; common case, reused instance
      (match-let* ([(.ρ m l) ρ]
                   [m′ (for/fold: : (Map (U Int Sym) .V) ([acc m∅]) ([sd sd*])
                         (let ([i (- l sd 1)])
                           (hash-set acc i (hash-ref m i))))])
        (.ρ m′ l))))

(: ρ+ : (case→ [.ρ .V → .ρ]
               [.ρ Sym .V → .ρ]))
(define ρ+
  (match-lambda*
    [(list (.ρ m l) (? .V? V)) (.ρ (hash-set m l V) (+ 1 l))]
    [(list (.ρ m l) (? sym? x) (? .V? V)) (.ρ (hash-set m x V) l)]))

(: ρ++ (case→ [.ρ (Listof .V) → .ρ]
              [.ρ (Listof .V) (U Bool Int) → .ρ]))
(define (ρ++ ρ V* [var? #f])
  (match var?
    [#f (for/fold ([ρi ρ]) ([V V*]) (ρ+ ρi V))]
    [0 (ρ+ ρ (foldr (λ: ([Vi : .V] [Vr : .V])
                      (.// (.St 'cons (list Vi Vr)) ∅))
                    MT V*))]
    [(? integer? n) (ρ++ (ρ+ ρ (car V*)) (cdr V*) (- n 1))]))

(: ρ@ : .ρ (U .x Int .x/c Sym) → .V)
(define (ρ@ ρ x)
  (match-let ([(.ρ m l) ρ])
    (hash-ref m (match x
                  [(.x sd) (- l sd 1)]
                  [(? int? sd) (- l sd 1)]
                  [(.x/c x) x]
                  [(? sym? x) x]))))

(: ρ-set : .ρ (U .x Int) .V → .ρ)
(define (ρ-set ρ x V)
  (match-let ([(.ρ m l) ρ]
              [sd (match x [(.x sd) sd] [(? int? sd) sd])])
    (.ρ (hash-set m (- l sd 1) V) l)))

(: ρ∋ : .ρ (U .x Int) → Bool)
(define (ρ∋ ρ x)
  (match-let ([(.ρ m l) ρ]
              [sd (match x [(.x sd) sd] [(? int? sd) sd])])
    (hash-has-key? m (- l sd 1))))


;;;;; STORE

;; store maps label indices to refined prevalues
(struct: .σ ([map : (Map Int (U .// .μ/V))] [next : Int]) #:transparent)
(define σ∅ (.σ (hash) 0))

(: σ@ : .σ (U .V Int) → .V)
(define (σ@ σ a)
  (match a
    [(.L i) (hash-ref (.σ-map σ) i)]
    [(? int? i) (hash-ref (.σ-map σ) i)]
    [(? .V? V) V]))

; allocates new location with given refinements.
; does NOT handle redundant/bogus refinements.
(: σ+ : .σ (U .V (Setof .V) #f) * → (Pairof .σ .L))
(define (σ+ σ . C*)
  (match-let ([(.σ m i) σ])
    (cons (.σ (hash-set m i
                        (match-let ([Cs (for/fold: ([a : (Setof .V) ∅]) ([C C*])
                                          (match C
                                            [(? set? s) (set-union a s)]
                                            [(? .V? C) (set-add a C)]
                                            [_ a]))])
                          (if (set-empty? Cs) ♦ (.// • Cs))))
              (+ 1 i))
          (.L i))))

(: σ++ : .σ Int → (Pairof .σ (Listof .L)))
(define (σ++ σ n)
  (match-let* ([(.σ m lo) σ]
               [hi (+ lo n)]
               [r (range lo hi)])
    (cons (.σ (for/fold ([m m]) ([i r]) (hash-set m i ♦)) hi)
          (for/list: : (Listof .L) ([i r]) (.L i)))))

(: σ-set : .σ (U .L Int) (U .// .μ/V) → .σ)
(define (σ-set σ a V)
  (match-let ([(.σ m l) σ]
              [i (match a [(.L i) i] [(? int? i) i])])
    (.σ (hash-set m i V) l)))

; substitute contract for given symbol
(: C/ : .V Sym .V → .V)
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
            (.λ↓ (.λ 1 (.@ (.=) (list (.x 0) (.@ o (list c d) 'Λ)) 'Λ) #f) ρ∅)]
           [((.// (? .b? c) _) _)
            (.λ↓ (.λ 1 (.@ (.=) (list (.x 0) (.@ o (list c (.x 1)) 'Λ)) 'Λ) #f) (ρ+ ρ∅ V2))]
           [(_ (.// (? .b? d) _))
            (.λ↓ (.λ 1 (.@ (.=) (list (.x 0) (.@ o (list (.x 1) d) 'Λ)) 'Λ) #f) (ρ+ ρ∅ V1))]
           [(_ _)
            (.λ↓ (.λ 1 (.@ (.=) (list (.x 0) (.@ o (list (.x 2) (.x 1)) 'Λ)) 'Λ) #f) (ρ++ ρ∅ (list V1 V2)))]))]))

(: V-abs : (case→ [.σ .V → .V]
                  [.σ (Listof .V) → (Listof .V)]
                  [.σ .ρ → .ρ]))
(define (V-abs σ V*)
  (: go : (case→ [.V → .V] [(Listof .V) → (Listof .V)] [.ρ → .ρ]))
  (define go
    (match-lambda
      [(.L i) (go (σ@ σ i))]
      [(and V (.// U C*))
       (match U
         [(.Ar C V′ l^3) (.// (.Ar (go C) (go V′) l^3) C*)]
         [(.St t V*′) (.// (.St t (map go V*′)) C*)]
         [(.λ↓ f ρ) (→V (.λ↓ f (go ρ)))]
         [_ (.// U
                 (for/set: .V ([C C*]
                               #:unless ; discard dynamically generated refinements
                               (match? C (.// (.λ↓ (.λ 1 (.@ (.=) (list (.x 0) _) 'Λ) #f) _) _)))
                   C))])] ; FIXME: ok to ignore other forms??
      [(? .V? V) V]
      [(? list? V*) (map go V*)]
      [(.ρ m l) (.ρ (for/fold ([m′ m]) ([x (in-hash-keys m)])
                      (hash-set m′ x (go (hash-ref m x)))) l)]))
  (go V*))

(define**
  [ZERO/C (→C (.=) #:2nd ZERO)]
  [POS/C (→C (.>) #:2nd ZERO)]
  [NEG/C (→C (.<) #:2nd ZERO)]
  [NON-NEG/C (→C (.≥) #:2nd ZERO)]
  [NON-POS/C (→C (.≤) #:2nd ZERO)]
  [ONE/C (→C (.=) #:2nd ONE)])
(define NON-ZERO/C (.¬/C ZERO/C))
(: sign/C : Real → (Setof .V))
(define (sign/C x) ; TODO ridiculous, yea...
  (cond [(> x 0) {set POS/C NON-NEG/C NON-ZERO/C}]
        [(= x 0) {set ZERO/C NON-NEG/C NON-POS/C}]
        [else {set NEG/C NON-ZERO/C NON-POS/C}]))

(:* [+/C -/C */C ÷/C] : .V .V → .V)
(define (+/C V1 V2) (→C (.+) #:1st V1 #:2nd V2))
(define (-/C V1 V2) (→C (.-) #:1st V1 #:2nd V2))
(define (*/C V1 V2) (→C (.*) #:1st V1 #:2nd V2))
(define (÷/C V1 V2) (→C (./) #:1st V1 #:2nd V2))

(:* [</C >/C ≥/C ≤/C =/C ≠/C] : .V → .V)
(define (</C V) (→C (.<) #:2nd V))
(define (>/C V) (→C (.>) #:2nd V))
(define (≥/C V) (→C (.≥) #:2nd V))
(define (≤/C V) (→C (.≤) #:2nd V))
(define (=/C V) (→C (.=) #:2nd V))
(define (≠/C V) (.¬/C (=/C V)))

(:* [arity=/C arity≥/C arity-includes/C] : Int → .V)
(define (arity=/C n) (→C (.arity=?) #:2nd (Prim n)))
(define (arity≥/C n) (→C (.arity≥?) #:2nd (Prim n)))
(define (arity-includes/C n) (→C (.arity-includes?) #:2nd (Prim n)))

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
          [(.λ 1 (.@ (.x i) (list (.x 0)) _) #f)
           (match (ρ@ ρ (- i 1))
             [(and o (.// (.o) _)) o]
             [(.// (.λ↓ (.λ 1 (.@ (? .v? v) (list (.x 0)) _) #f) ρ′) C*)
              (match v
                [(.•) ♦]
                [(? .prim? p) (→V p)]
                [(and (? .λ? f) (? closed? f)) (simplify (.// (.λ↓ f ρ∅) C*))]
                [_ V])]
             [_ V])]
          [(.λ 1 (.@ (? .v? v) (list (.x 0)) _) #f)
           (match v
             [(.•) ♦]
             [(? .prim? p) (→V p)]
             [(and (? .λ? f) (? closed? f)) (simplify (.// (.λ↓ f ρ∅) C*))]
             [_ V])]
          [(.λ 1 (.@ (.=) (list (.x 0) (.@ (.add1) (list e) l)) g) #f)
           (.// (.λ↓ (.λ 1 (.@ (.=) (list (.x 0) (.@ (.+) (list e .one) l)) g) #f) ρ) C*)]
          [(.λ 1 (.@ (.=) (list (.x 0) (.@ (.sub1) (list e) l)) g) #f)
           (.// (.λ↓ (.λ 1 (.@ (.=) (list (.x 0) (.@ (.-) (list e .one) l)) g) #f) ρ) C*)]
          [_ V])]
       [_ V])]
    [_ V]))

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

(: unroll/C : .μ/C → .V)
(define (unroll/C U) (match-let ([(.μ/C x C′) U]) (C/ C′ x (→V U))))

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
      [(? .ρ? (and ρ (.ρ m l)))
       (let ([m′ (for/fold: ([m′ : (Map (U Int Sym) .V) m∅]) ([x (in-hash-keys m)])
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
  (let ([xs (let: col : (Setof Sym) ([V : (U .V (Setof .V) (Listof .V)) V])
              (match V
                [(.L _) ∅]
                [(.// U C*)
                 (match U
                   [(.Ar _ V _) (col V)]
                   [(.St _ Vs) (col Vs)]
                   [_ ∅])] ; TODO ok to ignore?
                [(.μ/V x Vs) (col Vs)]
                [(.X/V x) {set x}]
                [(? set? V*) (for/fold: ([s : (Setof Sym) ∅]) ([V V*])
                               (set-union s (col V)))]
                [(? list? V*) (for/fold: ([s : (Setof Sym) ∅]) ([V V*])
                                (set-union s (col V)))]))])
    (variable-not-in (set->list xs) 'X)))

(: flat/C? : .σ (U .U .V) → Bool)
(define (flat/C? σ V) ; returns whether value is definitely a flat contract
  (let go ([V V])
    (match V
      [(.L i) (go (σ@ σ i))]
      [(.// U _) (go U)]
      [(.μ/V _ V*) (for/and ([V V*]) (go V))]
      [(.St/C _ C*) (andmap go C*)]
      [(.St _ C*) (andmap go C*)]      
      [(.μ/C _ D) (go D)]
      [(? .Λ/C?) #f]
      [_ #t])))

(: trace-cycle : .λ .ρ → (Setof .V))
(define (trace-cycle e ρ)
  (define-set: ac : .V [_ add!])
  (: go-V : .V → Void)
  (define (go-V V)
    (match V
      [(.// (.λ↓ f ρ1) _) (if (equal? #|eq?|# f e) (add! V) (go-ρ ρ1))]
      [(.// (.Ar _ V′ _) _) (go-V V′)]
      [_ (void)]))
  (: go-ρ : .ρ → Void)
  (define (go-ρ ρ)
    (match-let ([(.ρ m _) ρ])
      (for ([V (in-hash-values m)]) (go-V V))))
  (go-ρ ρ)
  ac)

(: ≃ : (case→ [.σ .V .σ .V → (Option .F)]
              [.σ (Listof .V) .σ (Listof .V) → (Option .F)]))
(define (≃ σ0 x0 σ1 x1)
  
  (define-syntax-rule (∪ F G)
    (match F
      [(? set? f) (match G [(? set? g) (set-union f g)] [_ #f])]
      [_ #f]))
  
  (: go : (case→ [.V .V → (Option .F)]
                 [(Listof .V) (Listof .V) → (Option .F)]
                 [.ρ .ρ → (Option .F)]))
  (define (go x0 x1)
    (match* (x0 x1)
      ; TODO assume always consistent for now
      [((? list? l0) (? list? l1))
       (let loop ([l0 l0] [l1 l1])
         (match* (l0 l1)
           [('() '()) ∅]
           [((cons V0 l0) (cons V1 l1)) (∪ (go V0 V1) (loop l0 l1))]))]
      [((.ρ m0 l0) (.ρ m1 l1))
          (for/fold: ([s : (Option .F) ∅]) ([i (in-range 0 (max l0 l1))])
            (match* ((hash-ref m0 (- l0 i 1)) (hash-ref m1 (- l1 i 1)))
              [((? .V? V0) (? .V? V1)) (∪ s (go V0 V1))]
              [(#f #f) s]
              [(_ _) #f]))]
      [((.// U0 C0s) (.// U1 C1s))
       (match* (U0 U1)
         [((.Ar C0 V0 _) (.Ar C1 V1 _)) (∪ (go V0 V1) (go C0 C1))]
         [((.St t V0*) (.St t V1*)) (go V0* V1*)]
         [((.λ↓ e ρ0) (.λ↓ e ρ1)) (go ρ0 ρ1)]
         [((.Λ/C C0* (.↓ e ρ0) v?) (.Λ/C C1* (.↓ e ρ1) v?)) (∪ (go C0* C1*) (go ρ0 ρ1))]
         [(U U) (if (equal? C0s C1s) ∅ #f)])]
      [((and L0 (.L i)) (and L1 (.L j))) (∪ (go (σ@ σ0 i) (σ@ σ1 j)) (set (cons L0 L1)))]
      [(_ _) (if (equal? x0 x1) ∅ #f)]))
  
  (go x0 x1))