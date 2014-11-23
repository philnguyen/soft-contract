#lang typed/racket/base
(require racket/match racket/set racket/list
         "../utils.rkt" "../lang.rkt")
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

(: →V : .U → .//)
(define (→V U) (.// U ∅))

;; maps abstract to concrete labels
(define-type .F (Map Int Int))
(define: F∅ : .F (hash))
(define .F? hash?)

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
                [#f (match-let ([(cons σ′ (and L_j (.L j))) (σ+ σ-new)])
                      (set! σ-new σ′)
                      (set! F (hash-set F i j))
                      (let ([V′ (go! (σ@ σ-old i))])
                        (set! σ-new (σ-set σ-new j V′))
                        L_j))])]
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
        (for/fold: : (Map (U Sym Int) .V) ([acc : (Map (U Sym Int) .V) m]) ([k (in-hash-keys m)])
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
                   [(.λ↓ f (.ρ m _)) (for/and: : Bool ([V (in-hash-values m)])
                                       (transfer? V))]
                   [(.Λ/C C (.ρ m _) _)
                    (and (andmap transfer? C)
                         (for/and: : Bool ([V (in-hash-values m)])
                           (transfer? V)))]
                   [(.St/C _ C*) (andmap transfer? C*)]
                   [(.μ/C _ c) (transfer? c)]
                   [(? .X/C?) #t])]
      [_ #f]))
  
  (: well-formed? : .σ .V → Boolean)
  (define (well-formed? σ V)
    (match V
      [(.// U C*)
       (and (for/and: : Boolean ([C C*]) (well-formed? σ C))
            (match U
              [(.St _ V*) (for/and: : Boolean ([Vi V*]) (well-formed? σ Vi))]
              [(.λ↓ _ (.ρ m _))
               (for/and: : Boolean ([i (in-hash-keys m)])
                 (well-formed? σ (hash-ref m i)))]
              [_ #t]))]
      [(.L i) (and (hash-has-key? (.σ-map σ) i)
                   (well-formed? σ (σ@ σ i)))]
      [_ #t]))
  
  (let ([V-new (go! V-old)])
    #;(unless (well-formed? σ-new V-new)
      (error "malformed"))
    (list σ-new V-new F)))

;;;;; REUSED CONSTANTS

(: Prim : (U Sym Num String Bool) → .V)
(define Prim
  (memoize
   #:eq? #t
   (match-lambda
     [(or 'mt 'empty) MT]
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
  [STR/C (Prim 'str?)] [PROC/C (Prim 'proc?)] [SYM/C (Prim 'symbol?)])


;;;;; ENVIRONMENT

;; environment maps static distances (HACK: or symbols) to values
(struct: .ρ ([map : (Map (U Int Sym) .V)] [len : Int]) #:transparent) ; FIXME equality
(define ρ∅ (.ρ m∅ 0))

(: restrict : .ρ (Setof Int) → .ρ)
(define (restrict ρ sd*)
  (if (set-empty? sd*) ρ∅ ; common case, reuse instance
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

(: σ@ : (case→ [.σ (U .L Int) → (U .// .μ/V)]
               [.σ .// → .//]
               [.σ .μ/V → .μ/V]
               [.σ .X/V → .X/V]
               [.σ .V → .V]))
(define (σ@ σ a)
  (match a
    [(.L i) (hash-ref (.σ-map σ) i)]
    [(? int? i) (hash-ref (.σ-map σ) i)]
    [(and (? .V? V) (not (? .L?))) V]))

; allocates new location with given refinements.
; does NOT handle redundant/bogus refinements.
(: σ+ : .σ (U .V (Setof .V) #f) * → (Pairof .σ .L))
(define (σ+ σ . C*)
  (match-let ([(.σ m i) σ])
    (cons (.σ (hash-set m i
                        (match-let ([Cs (for/fold: ([a : (Setof .V) ∅]) ([C C*])
                                          (match C
                                            [(? set? s) (set-union a s)]
                                            [(? .V? C) (when (match? C (.// (.•) _)) (error "ha!")) (set-add a C)]
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
          (map .L r))))

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

(: sqrt/C : .V → .V)
(define (sqrt/C V)
  (→V
   (match V
     [(.// (? .b? b) _) (.λ↓ (.λ 1 (.@ (.=) (list (.x 0) (.@ (.sqrt) (list b) 'Λ)) 'Λ) #f) ρ∅)]
     [_ (.λ↓ (.λ 1 (.@ (.=) (list (.x 0) (.@ (.sqrt) (list (.x 1)) 'Λ)) 'Λ) #f) (ρ+ ρ∅ V))])))
 
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
          [(.λ 1 (.@ (.x i) (list (.x 0)) _) #f) (simplify (ρ@ ρ (- i 1)))]
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
       [(.Ar (.// (.Λ/C (list (.// (.λ↓ (.λ 1 (.b #t) _) _) _)) (.↓ (.bool?) _) _) _)
             (and p (.// (or (? .pred?) (? .st-p?)) _)) _)
        p]
       [(.Ar (.// (.Λ/C (list (.// (.λ↓ (.λ 1 (.b #t) _) _) _) ...) (.↓ (.λ 1 (.b #t) _) _) _) _)
             V _)
        (simplify V)]
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

(: unroll : .μ/V → (Setof .V))
(define (unroll V)
  (match-let ([(.μ/V x V*) V]) (V/ V* (.X/V x) V)))

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
      [(and ρ (.ρ m l))
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

;; return all sub-values as lambdas with similar function body
(: repeated-lambdas : .λ .ρ → (Setof .V))
(define (repeated-lambdas e ρ)
  (define-set: ac : .V [_ add!])
  (: go! : (U .V .ρ) → Void)
  (define go!
    (match-lambda
      [(and V (.// (.λ↓ f ρ1) _)) (if (equal? f e) (add! V) (go! ρ1))]
      [(.// (.Ar _ V′ _) _) (go! V′)]
      [(.ρ m _) (for ([V (in-hash-values m)]) (go! V))]
      [_ (void)]))
  (go! ρ)
  ac)
