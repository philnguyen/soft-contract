#lang racket
(require racket "syntax.rkt")

(provide
 #;(all-defined-out)
 (combine-out ; contract-wrapped version
  (contract-out
   [struct p ([ms (hash/c l? m?)] [e e?])]
   [struct m ([decs (hash/c l? c?)] [defs (hash/c l? v?)])]
   [struct • ()]
   [struct f ([arity int?] [e e?] [var? boolean?])]
   [struct op ([name o-name?])]
   [struct struct-mk ([name l?] [arity int?])]
   [struct struct-p ([name l?] [arity int?])]
   [struct struct-ac ([name l?] [arity int?] [index int?])]
   [struct x ([sd int?])]
   [struct ref ([from l?] [to l?] [x l?])]
   [struct @ ([ctx l?] [f e?] [xs (listof e?)])]
   [struct if/ ([test e?] [then e?] [else e?])]
   [struct amb ([e (listof e?)])]
   [struct func-c ([xs (listof c?)] [y c?] [var? boolean?])]
   [struct and-c ([l c?] [r c?])]
   [struct or-c ([l c?] [r c?])]
   [struct struct-c ([name l?] [fields (listof c?)])]
   [struct μ-c ([x l?] [c c?])]
   [clo-circular? (V? . -> . boolean?)]
   
   [pred/c ((or/c c? p-name?) . -> . c?)]
   [pred/C ((or/c c? p-name?) . -> . C?)]
   [>/C (V? . -> . C?)]
   [≥/C (V? . -> . C?)]
   [</C (V? . -> . C?)]
   [≤/C (V? . -> . C?)]
   [=/C (V? . -> . C?)]
   [≠/C (V? . -> . C?)]
   [not-c (c? . -> . c?)]
   [not-C (C? . -> . C?)]
   [sum/C (V? V? . -> . C?)]
   [dif/C (V? V? . -> . C?)]
   
   [subst/c (c? x-c? c? . -> . c?)]
   [FV ([e?] [int?] . ->* . [set/c int?])]
   [FV-c ([c?] [int?] . ->* . [set/c int?])]
   [flat? (c? . -> . any/c)]
   [with-havoc (p? . -> . p?)]
   
   [struct ρ ([m (hash/c int? V?)] [len integer?])]
   [ρ+ (ρ? V? . -> . ρ?)]
   [ρ++ ((ρ? (listof V?)) ((or/c #f int?)) . ->* . ρ?)]
   [ρ@ (ρ? (or/c x? int?) . -> . V?)]
   [ρ-has? (ρ? (or/c x? int?) . -> . any/c)]
   [ρ-restrict (ρ? (set/c int?) . -> . ρ?)]
   [ρ-set (ρ? (or/c x? int?) V? . -> . ρ?)]
   
   [struct σ ([m (hash/c L? V?)] [next L?])]
   [σ@ (σ? L? . -> . V?)]
   [σ@* (σ? V? . -> . V?)]
   [σ+ (σ? . -> . (cons/c σ? L?))]
   [σ++ (σ? integer? . -> . (cons/c σ? [listof L?]))]
   [σ-set (σ? L? V? . -> . σ?)]
   
   [struct close ([x any/c] [ρ ρ?])]
   [struct val ([pre any/c] [refinements (set/c C?)])]
   [struct Arr ([f+ l?] [f- l?] [fo l?] [C (close/c func-c?)] [V V?])]
   [struct Struct ([name l?] [fields (listof V?)])]
   [struct Blm ([f+ l?] [fo l?] [msg string?])]
   [struct Mon ([l+ l?] [l- l?] [lo l?] [c C?] [e E?])]
   [struct FC ([lo l?] [c C?] [v V?])]
   [struct Assume ([v V?] [c C?])]
   
   [arity-ok? (V? integer? . -> . [or/c 'Y 'N '?])]
   [min-arity-ok? (V? integer? . -> . [or/c 'Y 'N '?])]
   [opaque? ([E?] [integer?] . ->* . any/c)]
   
   [m∅ hash?] [ρ∅ ρ?] [σ∅ σ?] [★ val?]
   [prim (symbol? . -> . [or/c e? #f])]
   [checks# ((or/c p? e? c? m?) . -> . int?)])
  l? e? c? v? b? o? c? flat-c? x-c? V? L? U? F? A? C? E?
  int? o-name? p-name? p-name-total? pred? total-pred?
  close/c val/c bl))

(define l? symbol?)
(define int? integer?)


;;;;; SYNTAX

; program and module
(struct p (ms e) #:transparent)
(struct m (decs defs) #:transparent)

; expresion
(define (e? x) ([or/c v? x? ref? @? if/? amb?] x))

; value
(define (v? x) ([or/c f? b? •?] x))
(struct • () #:transparent)
(struct f (arity e var?) #:transparent)
(define (b? x) ([or/c number? boolean? string? symbol? o?] x))

; primitive ops
(define (o? x) ([or/c struct-mk? struct-ac? struct-p? op?] x))
(struct op (name) #:transparent)
(define (o-name? x) ; checks for valid primitive op's name
  (or (p-name? x) (hash-has-key? non-preds x)))
(define (p-name? x) ; checks for predicate's name
  (or (p-name-total? x) (hash-has-key? partial-preds x)))
(define (p-name-total? x) ; checks for total predicate's name
  (hash-has-key? total-preds x))
(define (pred? v) ; checks for predicate
  (match? v [? struct-p?] [op (? p-name?)]))
(define (total-pred? v) ; checks for total predicate
  (match? v [? struct-p?] [op (? p-name-total?)]))

; struct primitive ops
(struct struct-mk (name arity) #:transparent)
(struct struct-p (name arity) #:transparent)
(struct struct-ac (name arity index) #:transparent)

; local variable, using static distance
(struct x (sd) #:transparent)

; module reference
(struct ref (from to x)
  #:transparent
  #:methods ; FIXME: get rid of this hack
  gen:equal+hash
  [(define (equal-proc a b equal?-rec)
     (match* (a b)
       [([ref l1 g x] [ref l2 g x]) #t]
       [(_ _) #f]))
   (define (hash-proc a hash-rec)
     (match-let ([(ref _ g x) a])
       (+ [hash-rec g] (* 3 [hash-rec x]))))
   (define (hash2-proc a hash-rec)
     (match-let ([(ref _ g x) a])
       (+ [hash-rec g] (* 7 [hash-rec x]))))])

; application
(struct @ (ctx f xs)
  #:transparent
  #:methods
  gen:equal+hash
  [(define (equal-proc a b equal?-rec)
     (match* (a b)
       [([@ _ f1 xs1] [@ _ f2 xs2])
        (and (equal?-rec f1 f2) (equal?-rec xs1 xs2))]
       [(_ _) #f]))
   (define (hash-proc a hash-rec)
     (match a
       [(@ _ f xs) (+ [hash-rec f] (* 3 [hash-rec xs]))]))
   (define (hash2-proc a hash-rec)
     (match a
       [(@ _ f xs) (+ [hash-rec f] (* 7 [hash-rec xs]))]))])

; conditional
(struct if/ (test then else) #:transparent)

; for use in havoc to speed up convergence and avoid excessive garbage
(struct amb (e) #:transparent)

; contract
(define flat-c? v?)
(struct func-c (xs y var?) #:transparent)
(struct and-c (l r) #:transparent)
(struct or-c (l r) #:transparent)
(struct struct-c (name fields) #:transparent)
(struct μ-c (x c) #:transparent)
(define x-c? symbol?)
(define c? (or/c flat-c? func-c? and-c? or-c? struct-c? μ-c? x-c?))

(define not-c
  (match-lambda
    [(and-c l r) (or-c (not-c l) (not-c r))]
    [(or-c l r) (and-c (not-c l) (not-c r))]
    [(f 1 e #f) (f 1 (@ 'Δ (op 'false?) (list e)) #f)]
    [(? pred? p) (f 1 (@ 'Δ (op 'false?) (list (@ 'Δ p (list (x 0))))) #f)]
    [_ (error "not-c not valid for func/c, and not supported for struct/c, μ/c yet")]))

(define pred/c
  (match-lambda
    [(? c? c) c]
    [(? p-name? n) (prim p)]))
(define pred/C
  (match-lambda
    [(? c? c) (close c ρ∅)]
    [(? p-name? n) (close (prim p) ρ∅)]))

(define (not-C C)
  (match-let ([(close c ρ) C]) (close (not-c c) ρ)))

(define (rel/C R V)
  (match V
    [(val (? number? n) _) (close (f 1 (@ 'Δ R (list (x 0) n)) #f) ρ∅)]
    [_ (close (f 1 (@ 'Δ R (list (x 0) (x 1))) #f) (ρ+ ρ∅ V))]))
(define (>/C V) (rel/C (op '>) V))
(define (≥/C V) (rel/C (op '>=) V))
(define (</C V) (rel/C (op '<) V))
(define (≤/C V) (rel/C (op '<=) V))
(define (=/C V) (rel/C (op 'equal?) V))
(define (≠/C V) (not-C (rel/C (op 'equal?) V)))
(define (rel2/C f U V)
  (match* (U V)
    [((val (? number? m) _) (val (? number? n) _))
     (close (f 1 (@ 'Δ (op 'equal?) (list (x 0) (@ 'Δ f (list m n)))) #f) ρ∅)]
    [((val (? number? m) _) _)
     (close (f 1 (@ 'Δ (op 'equal?) (list (x 0) (@ 'Δ f (list m (x 1))))) #f)
            (ρ+ ρ∅ V))]
    [(_ (val (? number? n) _))
     (close (f 1 (@ 'Δ (op 'equal?) (list (x 0) (@ 'Δ f (list (x 1) n)))) #f)
            (ρ+ ρ∅ U))]
    [(_ _)
     (close (f 1 (@ 'Δ (op 'equal?) (list (x 0) (@ 'Δ f (list (x 1) (x 2))))) #f)
            (ρ++ ρ∅ (list V U)))]))
(define (sum/C U V) (rel2/C (op '+) U V))
(define (dif/C U V) (rel2/C (op '-) U V))

; substitute contract
(define (subst/c c1 x c2)
  (match c1
    [(func-c cx cy v?)
     (func-c (for/list ([cxi cx]) (subst/c cxi x c2))
             (subst/c cy x c2)
             v?)]
    [(and-c ca cb) (and-c [subst/c ca x c2] [subst/c cb x c2])]
    [(or-c ca cb) (or-c [subst/c ca x c2] [subst/c cb x c2])]
    [(struct-c t cs) (struct-c t (for/list ([ci cs]) (subst/c ci x c2)))]
    [(μ-c z c′) (if (equal? z x) c1 (μ-c z (subst/c c′ x c2)))]
    [(? symbol? z) (if (equal? x z) c2 z)]
    [_ c1]))

;; returns all free variables in terms of static distance
;; e.g. in (λx.λy.λz.(z + x)):
;;           FV (λz...) is {1}
;;           FV (λy...) is {0}
(define (FV e [depth 0])
  (match e
    [(x k) (if (>= k depth) {set (- k depth)} ∅)]
    [(f n e1 _) (FV e1 [+ depth n])]
    [(@ _ f xs) (for/fold ([acc (FV f depth)]) ([x xs])
                  (set-union acc (FV x depth)))]
    [(if/ e1 e2 e3) (set-union [FV e1 depth] [FV e2 depth] [FV e3 depth])]
    [(amb es) (for/fold ([acc ∅]) ([ei es])
                (set-union acc (FV ei depth)))]
    [_ ∅]))

(define (FV-c c [depth 0])
  (match c
    [(func-c cx cy _)
     (for/fold ([acc (FV-c cy [+ (length cx) depth])]) ([ci cx])
       (set-union acc [FV-c ci depth]))]
    [(or (and-c c1 c2) (or-c c1 c2)) (set-union (FV-c c1 depth) (FV-c c2 depth))]
    [(struct-c _ cs)
     (for/fold ([acc ∅]) ([ci cs]) (set-union acc [FV-c ci depth]))]
    [(μ-c _ c1) (FV-c c1 depth)]
    [(? symbol?) ∅]
    [(? v? v) (FV v depth)]))

;; checks whether a contract is flat
(define (flat? c)
  (match? c
    (and-c (? flat?) (? flat?))
    (or-c (? flat?) (? flat?))
    (struct-c _ (list (? flat?) ...))
    (μ-c _ (? flat?))
    (? flat-c?)
    (? x-c?)))

;; generate havoc function for a program
(define (with-havoc prog)
  (match-define (p ms e†) prog)
  
  (define all-acs
    (set->list ; collect all public accessors
     (for*/fold ([acc {set (prim 'car) (prim 'cdr)}])
       ([(_ m) ms] [(_ c) (m-decs m)] #:when (match? c (func-c _ (? struct-c?) #f)))
       (match-let* ([(func-c _ (struct-c t cs) _) c]
                    [n (length cs)])
         (for/fold ([acc acc]) ([i n])
           (set-add acc (struct-ac t n i)))))))
  
  (cond
    [(hash-has-key? ms '☠) prog]
    [else
     (let ([havoc
            (f 1 (amb (cons [@ '☠ (ref '☠ '☠ 'havoc) ; (havoc (x •))
                               (list [@ '☠ [x 0] (list (•))])]
                            (for/list ([ac all-acs]) ; (havoc (accessor x)) ...
                              (@ '☠ (ref '☠ '☠ 'havoc)
                                 (list [@ '☠ ac (list [x 0])])))))
               #f)])
       (p (hash-set ms '☠ (m m∅ (hash 'havoc havoc))) e†))]))

(define (clo-depth-more-than? n V)
  (or (<= n 0)
      (match V
        [(val (close _ (ρ m _)) _)
         (for/or ([Vi (in-hash-values m)])
           (clo-depth-more-than? (- n 1) Vi))]
        [_ #f])))

(define (clo-circular? V)
  (match V
    [(val (close e (ρ m _)) _)
     (define (circ? V1)
       (match V1
         [(val (close e1 (ρ m1 _)) _)
          (or (eq? e1 e)
              (for/or ([Vi (in-hash-values m1)]) (circ? Vi)))]
         [_ #f]))
     (for/or ([V (in-hash-values m)]) (circ? V))]
    [_ #f]))

;;;;; ENVIRONMENT

; run-time environment mapping static distances to closures
(struct ρ (m len)
  #:transparent
  ; ignore environment length when comparing
  #:methods
  gen:equal+hash
  [(define (equal-proc ρ1 ρ2 equal?-rec)
     (match* (ρ1 ρ2)
       [([ρ m1 l1] [ρ m2 l2])
        (for/and ([sd (in-range 0 (max l1 l2)) #|max static distance|#])
          (if (ρ-has? ρ1 sd)
              (and (ρ-has? ρ2 sd) (equal?-rec (ρ@ ρ1 sd) (ρ@ ρ2 sd)))
              (not (ρ-has? ρ2 sd))))]
       [(_ _) #f]))
   (define (hash-proc a hash-rec)
     (match-let ([(ρ m _) a])
       (hash-rec (hash-values m))))
   (define (hash2-proc a hash-rec)
     (match-let ([(ρ m _) a])
       (hash-rec (hash-values m))))])

; extends environment with 1 or more closures
(define (ρ+ ρ1 V)
  (match-let ([(ρ m l) ρ1])
    (ρ (hash-set m l V) (add1 l))))

(define (ρ++ ρ1 V* [varargs? #f])
  (define MT (val [Struct 'empty '()] ∅))
  (match varargs?
    [#f (for/fold ([ρi ρ1]) ([V V*])
          (ρ+ ρi V))]
    [0 (ρ+ ρ1 (foldr (λ (Vi Vr) (val (Struct 'cons (list Vi Vr)) ∅)) MT V*))]
    [n (ρ++ (ρ+ ρ1 (car V*)) (cdr V*) (- n 1))]))

; access environment at given static distance
(define (ρ@ ρ1 x1)
  (match-let ([(ρ m l) ρ1]
              [sd (match x1 [(x sd) sd] [_ x1])])
    (hash-ref m (- l sd 1))))

;; modify environment at given static distance
(define (ρ-set ρ1 x1 V)
  (match-let ([(ρ m l) ρ1]
              [sd (match x1 [(x sd) sd] [_ x1])])
    (ρ (hash-set m (- l sd 1) V) l)))

;; checks whether given static distance is in environment's domain
(define (ρ-has? ρ1 x1)
  (match-let ([(ρ m l) ρ1]
              [sd (match x1 [(x sd) sd] [_ x1])])
    (hash-has-key? m (- l sd 1))))

; restrict environment's domain to given set of static distances
(define (ρ-restrict ρ1 xs)
  (match-let* ([(ρ m len) ρ1]
               [m′ (for/fold ([acc m∅]) ([sd (in-set xs)])
                     (let ([i (- len sd 1)])
                       (hash-set acc i (hash-ref m i))))])
    (ρ m′ len)))

;; store
(struct σ (m next) #:transparent)

;; store reference
(define (σ@ σ1 l)
  (hash-ref (σ-m σ1) l))
(define (σ@* σ v)
  (match v
    [(? L? l) (σ@* σ [σ@ σ l])]
    [_ v]))

;; allocates new label initially mapping to a completely opaque value
;; returns <new-store, new-label>
(define (σ+ σ1)
  (match-let ([(σ m l) σ1])
    (cons [σ (hash-set m l ★) (add1 l)] l)))

;; allocates n labels initially mapping to completely opaque values
;; returns <new-store, new-labels>
(define (σ++ σ1 n)
  (match-let* ([(σ m lo) σ1]
               [hi (+ lo n)]
               [ls (range lo hi)])
    (cons [σ (foldl (λ (l m1) (hash-set m1 l ★)) m ls) hi] ls)))

;; updates store at given label
(define (σ-set σ1 l V)
  (match-let ([(σ m len) σ1])
    (σ (hash-set m l V) len)))


;;;;; CLOSURE

; closed 'thing'
(struct close (x ρ) #:transparent)
(define ((close/c p) x)
  (match? x (close [? p] _))) ; just a partial check

; closed value
(define (V? x)
  (match? x [? L?] [val (? U?) _]))
(define L? int?) ; heap label
(struct val (pre refinements) #:transparent)
(define ((val/c p) x)
  (match? x (val [? p] _)))

; pre-value
(define (U? x)
  (match? x [? b?] [close (? f?) _] (•) [? Arr?] [? Struct?]))
(struct Arr (f+ f- fo C V) #:transparent)
(struct Struct (name fields) #:transparent)

; closed function
(define F? (val/c [or/c (close/c f?) Arr? o?]))

; closed answer
(define (A? x) ([or/c V? Blm?] x))
(struct Blm (f+ fo msg) #:transparent)
(define-syntax-rule (bl l+ lo s a ...)
  (Blm l+ lo (format (string-append "[" s "]") a ...)))

; closed contract
(define C? (close/c c?))

; closed expression
(define (E? x) ([or/c [close/c e?] A? Mon? FC? Assume?] x))
(struct Mon (l+ l- lo c e) #:transparent)
(struct FC (lo c v) #:transparent)
(struct Assume (v c) #:transparent)

; checks whether the closed function handles given arity
; returns (Y|N|?)
(define (arity-ok? F n)
  (match F
    [(val [close (f m _ #f) _] _) (if (= m n) 'Y 'N)]
    [(val [close (f m _ #t) _] _) (if (<= [sub1 m] n) 'Y 'N)]
    [(val [Arr _ _ _ (close (func-c cx _ v?) _) _] _)
     (let ([m (length cx)])
       (if (if v? [<= (sub1 m) n] [= m n]) 'Y 'N))]
    [(val [or (? struct-ac?) (op (or 'add1 'sub1 'str-len)) (? pred?)] _)
     (if (= n 1) 'Y 'N)]
    [(val [op (or '+ '- '* '/ 'equal? '= '> '< '<= '>=)] _)
     (if (= n 2) 'Y 'N)]
    [(val [struct-mk _ m] _) (if (= m n) 'Y 'N)]
    [(val (•) Cs)
     (or (for/first ([Ci Cs] #:when (match Ci
                                      [(close [? func-c?] _) #t]
                                      [_ #f]))
           (match-let ([(close [func-c cx _ v?] _) Ci])
             (let ([m (length cx)])
               (if (if v? (<= [sub1 m] n) (= m n)) 'Y 'N))))
         '?)]
    [_ 'N]))

; checks whether the closed function handles given arity or higher
(define (min-arity-ok? F n)
  (match F
    [(val [close (f m _ #t) _] _) (if (<= [sub1 m] n) 'Y 'N)]
    [(val [Arr _ _ _ (close [func-c cx _ #t] _) _] _)
     (if (<= [sub1 (length cx)] n) 'Y 'N)]
    [(val (•) Cs)
     (or (for/first ([Ci Cs] #:when (match Ci
                                      [(close [? func-c?] _) #t]
                                      [_ #f]))
           ; TODO wrong
           (match-let ([(close [func-c cx _ v?] _) Ci])
             (if v? (if (<= [sub1 (length cx)] n) 'Y 'N) 'N)))
         '?)]
    [_ 'N]))

; check whether the closure is opaque up to given depth
(define (opaque? v [d 2])
  (match v
    [(or (? L?) (val (•) _) (close (•) _)) #t]
    [(val (Struct t Vs) _)
     (if (zero? d) #f
         (for/or ([Vi Vs])
           (opaque? Vi [sub1 d])))]
    [_ #f]))

; empty values, for re-use if possible
(define m∅ (hash))
(define ρ∅ (ρ m∅ 0))
(define σ∅ (σ m∅ 0))
(define ★ (val (•) ∅))

;; maps a primitive's name to the corresponding operator
(define total-preds
  (for/hash ([n '(any num? real? int? true? false? bool? str? symbol? proc?)])
    (values n (op n))))
(define partial-preds
  (for/hash ([n '(zero? positive? negative?)])
    (values n (op n))))
(define non-preds
  (hash-set* (for/hash ([n '(add1 sub1 + - * / str-len equal? = > < <= >=)])
               (values n (op n)))
             'cons (struct-mk 'cons 2)
             'car (struct-ac 'cons 2 0)
             'cdr (struct-ac 'cons 2 1)
             'cons? (struct-p 'cons 2)
             'empty #|hack|# (@ 'Δ (struct-mk 'empty 0) '())
             'empty? (struct-p 'empty 0)
             'not (op 'false?)))
(define (prim name)
  (or (hash-ref total-preds name (λ () #f))
      (hash-ref partial-preds name (λ () #f))
      (hash-ref non-preds name (λ () #f))))

;; rough estimate the number of unsafe operations that need dynamic checks
;; -- each application site contributes 1
;; -- each partial primitive operation contributes 1, regardless of arity
(define/match (checks# x)
  [((list x ...)) (for/sum ([xi x]) (checks# xi))]
  [((p ms e)) (+ (for/sum ([(l mi) (in-hash ms)] #:unless (equal? l '☠)) (checks# mi))
                 (checks# e))]
  [((m decs defs)) (+ (checks# (hash-values decs)) (checks# (hash-values defs)))]
  [((f _ e _)) (checks# e)]
  [((@ _ f xs)) (+ 1 #|for proc?|# (checks# f) (checks# xs))]
  [((if/ e0 e1 e2)) (+ (checks# e0) (checks# e1) (checks# e2))]
  [((amb es)) (checks# es)]
  [((or (and-c c d) (or-c c d))) (+ (checks# c) (checks# d))]
  [((μ-c _ c)) (checks# c)]
  [((func-c cx d _)) (+ (checks# cx) (checks# d))]
  [((or (? struct-mk?) (? total-pred?) (op 'equal?))) 0]
  [((? o?)) 1]
  [(_) 0])
