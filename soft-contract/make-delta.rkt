#lang typed/racket/base
(provide (all-defined-out))

(require
 racket/match racket/list racket/set racket/function racket/bool
 "utils.rkt" "lang.rkt" "runtime.rkt" "provability.rkt" "show.rkt"
 (for-syntax racket/base syntax/parse racket/contract racket/pretty racket/match
             racket/bool racket/list))

;; Specialized non-deterministic match for answers
(define-syntax-rule (match/Ans* v [p e ...] ...) (match/nd: (.Ans → .Ans) v [p e ...] ...))

(define (box-operation? [o : .o])
  (match o
    [(.st-mk (.id 'box 'Λ) _) #t]
    [(.st-ac (.id 'box 'Λ) _ _) #t]
    [(.st-p (.id 'box 'Λ) _) #t]
    [_ #f]))

#;(define X #'X)

(define refine1 : (Parameterof (.σ .V .V → .Vns))
  (make-parameter
   (λ (σ V C)
     (error 'Internal "Unparameterized `refine1`"))))

(: V=? : .σ .V .V → .Vns*)
(define (V=? σ V1 V2)
  (match* (V1 V2)
    [((.L i) (.L i)) (cons σ TT)]
    [((.L i) (and (.// (not (? .•?)) _) V2))
     (match/nd: (.Vns → .Vns) (V=? σ (σ@ σ i) V2)
       [(cons σt (.// (.b #t) _)) (cons (σ-set σt i V2) TT)]
       [a a])]
    [((and (.// (not (? .•?)) _) V1) (.L i))
     (match/nd: (.Vns → .Vns) (V=? σ V1 (σ@ σ i))
       [(cons σt (.// (.b #t) _)) (cons (σ-set σt i V1) TT)]
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
              (match/nd: (.Vns → .Vns) (V=? σ V1 V2)
                [(cons σt (.// (.b #t) _)) (loop σt V1* V2*)]
                [a a])]))
         (cons σ FF))]
    ; default
    [((.// U1 _) (.// U2 _)) (cons σ (Prim (equal? U1 U2)))]))

(: refine : .σ .V (U (Setof .V) (Listof .V) .V) * → .Vns)
(define (refine σ V . Css)
  (: go : .σ .V (Listof (U (Setof .V) (Listof .V) .V)) → .Vns)
  (define (go σ V Css)
    #;(log-debug "REFINE:~n~a~n~a~n~a~n~n" σ V Css)
    (match Css
      ['() (cons σ V)]
      [(cons (? list? Cs) Cᵣs)
       (match-define (cons σ′ V′)
         (for/fold ([σV : .Vns (cons σ V)]) ([C : .V Cs])
           (match-define (cons σ V) σV)
           (refine σ V C)))
       (go σ′ V′ Cᵣs)]
      [(cons (? set? Cs) Cᵣs)
       (match-define (cons σ′ V′)
         (for/fold ([σV : .Vns (cons σ V)]) ([C : .V Cs])
           (match-define (cons σ V) σV)
           (refine σ V C)))
       (go σ′ V′ Cᵣs)]
      [(cons (.// (.St (.id 'and/c 'Λ) Cs) _) Cᵣs)
       (go σ V (cons Cs Cᵣs))]
      [(cons (? .V? C) Cᵣs)
       (match (⊢ σ V C)
         ['✓ (cons σ V)]
         ['X (error 'Internal "Bogus refinement of ~a by ~a" (show-V σ V) (show-V σ C))]
         [_ (match-define (cons σ′ V′) ((refine1) σ V C))
            (go σ′ V′ Cᵣs)])]))
  (go σ V Css))

(: refine* : .σ (Listof .V) (Listof .V) → (Pairof .σ (Listof .V)))
(define (refine* σ V* C*)  
  (let-values ([(σ′ V*′)
                (for/fold ([σ : .σ σ] [Vs : (Listof .V) '()]) ([V V*] [C C*])
                  #;(log-debug "Got:~n~a~n~a~n~n" V C)
                  (match-let ([(cons σ V) ((refine1) σ V C)])
                    (values σ (cons V Vs))))])
    (cons σ′ (reverse V*′))))

(: check-C : .σ .V .V → .Vns*)
(define (check-C σ V C)
  (match (⊢ σ V C)
    ['✓ (cons σ TT)]
    ['X (cons σ FF)]
    ['?
     (match-define (cons σt _) (refine σ V C))
     (match-define (cons σf _) (refine σ V (.¬/C C)))
     {set (cons σt TT) (cons σf FF)}]))

(: check-o² : .σ .o2 .V .V → .Vns*)
(define (check-o² σ o V₁ V₂)
  (define W₁ (σ@ σ V₁))
  (define W₂ (σ@ σ V₂))
  (define X₁ (if (match? W₁ (.// (? .•?) _)) V₁ W₁))
  (define X₂ (if (match? W₂ (.// (? .•?) _)) V₂ W₂))
  (define C₂ (→C o #:2nd X₂))
  (match (⊢ σ X₁ C₂)
    ['✓ (cons σ TT)]
    ['X (cons σ FF)]
    ['?
     (define C₁ (→C o #:1st X₁))
     (match (⊢ σ X₂ C₁)
       ['✓ (cons σ TT)]
       ['X (cons σ FF)]
       ['?
        (match-define (cons σt _)
          (match* (X₁ X₂)
            [((.L i) (.L j))
             (if (> i j) (refine σ X₁ C₂) (refine σ X₂ C₁))]
            [((? .L?) _) (refine σ X₁ C₂)]
            [(_ (? .L?)) (refine σ X₂ C₁)]
            [(_ _) (cons σ 'ignore)]))
        (match-define (cons σf _)
          (match* (X₁ X₂)
            [((.L i) (.L j))
             (if (> i j) (refine σ X₁ (.¬/C C₂)) (refine σ X₂ (.¬/C C₁)))]
            [((? .L?) _) (refine σ X₁ (.¬/C C₂))]
            [(_ (? .L?)) (refine σ X₂ (.¬/C C₁))]
            [(_ _) (cons σ 'ignore)]))
        {set (cons σt TT) (cons σf FF)}])]))

(: refine-C* : (Setof .V) .V → (Setof .V))
(define (refine-C* Cs C)
  (cond [(set-empty? Cs) {set C}]
        [else (for/fold ([acc : (Setof .V) ∅]) ([Cᵢ Cs])
                (∪ acc (refine-C Cᵢ C)))]))

(: refine-C : .V .V → (U .V (Setof .V)))
(define (refine-C C D)
  (cond
    [(equal? '✓ (C⇒C C D)) C]
    [(equal? '✓ (C⇒C D C)) D]
    [else
     (match* (C D)
       [((.// Uc _) (.// Ud _))
        (match* (Uc Ud)
          ; unroll recursive ones
          [(_ (.μ/C x D′)) (refine-C C (C/ D′ x D))]
          [((.μ/C x C′) _) (refine-C (C/ C′ x C) D)]
          ; break conjunctive ones
          [(_ (.St (.id 'and/c 'Λ) (list D1 D2))) (∪ (refine-C C D1) (refine-C C D2))]
          [((.St (.id 'and/c 'Λ) (list C1 C2)) _) (∪ (refine-C C1 D) (refine-C C2 D))]
          ; prune impossible disjunct
          [(_ (.St (.id 'or/c 'Λ) _)) (let ([D′ (truncate D C)])
                                        (if (equal? D D′) {set C D} (refine-C C D′)))]
          [((.St (.id 'or/c 'Λ) _) _) (let ([C′ (truncate C D)])
                                        (if (equal? C C′) {set C D} (refine-C C′ D)))]
          ; special rules for reals
          [((.λ↓ (.λ 1 (.@ '>= (list e1 e2) l)) ρc)
            (.St (.id 'not/c 'Λ)
                 (list (.// (.λ↓ (.λ 1 (.@ (or '= 'equal?)
                                           (or (list e1 e2) (list e2 e1)) _)) ρd) _))))
           (if (equal? ρc ρd) (→V (.λ↓ (.λ 1 (.@ '> (list e1 e2) l)) ρc)) {set C D})]
          [((.St (.id 'not/c 'Λ)
                 (list (.// (.λ↓ (.λ 1 (.@ (or '= 'equal?)
                                           (or (list e1 e2) (list e2 e1)) _)) ρc) _)))
            (.λ↓ (.λ 1 (.@ '>= (list e1 e2) l)) ρd))
           (if (equal? ρc ρd) (→V (.λ↓ (.λ 1 (.@ '> (list e1 e2) l)) ρd)) {set C D})]
          [((.λ↓ (.λ 1 (.@ '<= (list e1 e2) l)) ρc)
            (.St (.id 'not/c 'Λ)
                 (list (.// (.λ↓ (.λ 1 (.@ (or '= 'equal?)
                                           (or (list e1 e2) (list e2 e1)) _)) ρd) _))))
           (if (equal? ρc ρd) (→V (.λ↓ (.λ 1 (.@ '< (list e1 e2) l)) ρc)) {set C D})]
          [((.St (.id 'not/c 'Λ)
                 (list (.// (.λ↓ (.λ 1 (.@ (or '= 'equal?)
                                           (or (list e1 e2) (list e2 e1)) _)) ρc) _)))
            (.λ↓ (.λ 1 (.@ '<= (list e1 e2) l)) ρd))
           (if (equal? ρc ρd) (→V (.λ↓ (.λ 1 (.@ '< (list e1 e2) l)) ρd)) {set C D})]
          [(_ _) {set C D}])]
       [(_ _) {set C D}])]))

;; throws away all branch in C excluded by D
(: truncate : .V .V → .V)
(define (truncate C D)
  (match C
    [(.// (.St (.id 'or/c 'Λ) (list C1 C2)) C*)
     (match* ((C⇒C D C1) (C⇒C D C2))
       [('X 'X) (error "WTF??")]
       [(_ 'X) (truncate C1 D)]
       [('X _) (truncate C2 D)]
       [(_ _) (.// (.St (.id 'or/c 'Λ) (list (truncate C1 D) (truncate C2 D))) C*)])]
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
                [(.St (? identifier? t) V*) {set (→V (.st-p t (length V*)))}]
                [_ ∅]))

(: b^ : (U Number String Symbol Boolean Keyword) → (Setof .V))
(define b^
  (match-lambda
    [(? integer? n) (set-union {set (Prim 'integer?) (Prim 'real?) (Prim 'number?)} (sign/C n))]
    [(? real? r) (set-union {set (Prim 'real?) (Prim 'number?)} (sign/C r))]
    [(? number? x) {set (Prim 'number?)}]
    [(? string?) {set (Prim 'string?)}]
    [(? symbol?) {set (Prim 'symbol?)}]
    [(? keyword? x) {set (Prim 'keyword?)}]
    [#t {set (.¬/C (Prim 'false?)) (Prim 'boolean?)}]
    [#f {set (Prim 'false?) (Prim 'boolean?)}]))

(: alloc : (case-> [.σ .V → .Vns]
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
                   (for/fold ([σ : .σ σ] [m′ : (Map (U Integer Symbol) .V) m])
                             ([x (in-hash-keys m)])
                     (match-let ([(cons σ V) (alloc σ (hash-ref m x))])
                       (values σ (hash-set m′ x V))))])
       (cons σ (→V (.λ↓ f (.ρ m l)))))]
    [(.// '• Cs)
     (let-values ([(σ L) (σ+ σ)])
       (refine σ L Cs))]
    [(? .μ/V? V)
     (let-values ([(σ L) (σ+ σ)])
       (cons (σ-set σ L V) L))]
    [(? .V? V) (cons σ V)]
    [(? list? V*) (let-values ([(σ Vs)
                                (for/fold ([σ : .σ σ] [Vs : (Listof .V) '()]) ([V V*])
                                  (match-let ([(cons σ V) (alloc σ V)])
                                    (values σ (cons V Vs))))])
                    (cons σ (reverse Vs)))]))

;; Language definition for `δ` begins here 
(begin-for-syntax
  
  (define/contract -σ (parameter/c identifier?) (make-parameter #f))
  (define/contract -l (parameter/c identifier?) (make-parameter #f))
  
  (define/contract fresh-id! (-> identifier?)
    (let ([n 0])
      (λ ()
        (set! n (+ 1 n))
        (datum->syntax #f (string->symbol (format "x~a" n))))))
  
  (define-syntax-class real
    #:description "real number literal"
    (pattern x:number
             #:fail-unless
             (real? (syntax->datum #'x))
             "non-real number literal"))
  
  (define-syntax-class atom
    #:description "identifier or simple value"
    (pattern (~or x:id x:boolean x:number x:str x:char)))
  
  (define-syntax-class term
    #:description "simple term"
    (pattern (~or t:atom (o:o² l:atom r:atom) #;(o:op¹ l:lit-or-id))))
  
  (define-syntax-class o²
    #:description "restricted binary operator"
    (pattern (~or (~literal +) (~literal -) (~literal *) (~literal /) (~literal expt)
                  (~literal remainder))))
  
  (define-syntax-class b
    #:description "[identifier : contract]"
    (pattern [x:id (~literal :) c:ctc]))
  
  (define-syntax-class sig
    #:description "simple signature"
    (pattern (c:ctc ... (~literal →) d:ctc)))
  
  (define-syntax-class ctc
    #:description "restricted first-order contract"
    (pattern (~or c:id
                  (~literal any/c)
                  ((~literal >/c) x:atom) ((~literal ≥/c) x:atom)
                  ((~literal </c) x:atom) ((~literal ≤/c) x:atom)
                  ((~literal =/c) x:term) ((~literal ≡/c) x:atom)
                  ((~literal ¬) d:ctc)
                  ((~literal ∧) e:ctc ...) ((~literal ∨) e:ctc ...))))
  
  (define-syntax-class dom
    #:description "list of contracts for domain"
    (pattern (c:ctc ...)))
  
  (define-syntax-class decl
    #:description "primary signature"
    (pattern (⋆:id (~literal :) x:b ... (~literal →) rng:ctc)))
  
  (define/contract (doms-arg-count-different? doms n)
    ((listof syntax?) integer? . -> . (or/c #f syntax?))
    (for/or ([dom (in-list doms)])
      (cond [(= n (length (syntax->list dom))) #f]
            [else dom])))
  
  (define/contract (refinements-arg-count-different? sigs n)
    ((listof syntax?) integer? . -> . (or/c #f syntax?))
    (for/or ([sig (in-list sigs)])
      (syntax-parse sig
        #:literals (→)
        [(x:ctc ... → _)
         (cond [(= n (length (syntax->list #'(x ...)))) #f]
               [else #'(x ...)])])))
  
  (define/contract (arg-count-inconsistent? dec doms sigs)
    (syntax? (listof syntax?) (listof syntax?) . -> . (or/c #f syntax?))
    (syntax-parse dec
      #:literals (: →)
      [(_ : x:b ... → _)
       (define n (length (syntax->list #'(x ...))))
       (or (doms-arg-count-different? doms n)
           (refinements-arg-count-different? sigs n))]))
  
  (define-syntax-class δ-clause
    #:description "δ-clause"
    (pattern [#:escape (o:expr args:expr) body:expr ...])
    (pattern [dec:decl #:other-errors dom:dom ... #:refinements refinement:sig ...]
             #:fail-when
             (arg-count-inconsistent? #'dec
                                      (syntax->list #'(dom ...))
                                      (syntax->list #'(refinement ...)))
             "inconsistent argument counts")
    (pattern [#:predicate op:id (~literal :) c:ctc ...])
    ;; Shorthands:
    (pattern [dec:decl])
    ;; TODO how to specify "optional-ness"?
    (pattern [dec:decl #:other-errors dom:dom ...]  
             #:fail-when
             (arg-count-inconsistent? #'dec (syntax->list #'(dom ...)) '())
             "inconsistent argument counts")
    (pattern [dec:decl #:refinements refinement:sig ...]
             #:fail-when
             (arg-count-inconsistent? #'dec '() (syntax->list #'(refinement ...)))
             "inconsistent argument counts")
    (pattern [#:predicate op:id]))
  
  (define-syntax-class match-clause
    #:description "regular match clause"
    (pattern [(o:expr args:expr) body:expr ...]))
  
  (define/contract (parse-arith dec err-doms refinements)
    (syntax? (listof syntax?) (listof syntax?) . -> . syntax?)
    (syntax-parse (list dec err-doms refinements)
      #:literals (: →)
      [((⋆ : [x : c] ... → d)
        ((cₑ ...) ...)
        ((cᵣ ... → dᵣ) ...))
       (define xs (syntax->list #'(x ...)))
       (define cs (syntax->list #'(c ...)))
       #`[('⋆ (list x ...))
          #,(gen-guards
             #'⋆
             xs
             cs
             (gen-other-guards
              #'⋆
              xs 
              (map syntax->list (syntax->list #'((cₑ ...) ...)))
              (gen-result #'⋆ xs cs #'d (syntax->list #'((cᵣ ... → dᵣ) ...)))))]]))
  
  ;; Generate code checking arguments `xs` against contracts `cs` pairwise
  (define/contract (gen-guards o xs cs kont)
    (identifier? (listof syntax?) (listof syntax?) syntax? . -> . syntax?)
    
    (with-syntax ([σ (-σ)] [l (-l)])
      (foldr (λ (x c rest)
               (syntax-parse c
                 [(~literal any/c) rest]
                 [_
                  (define-values (compute-C id-C)
                    (let ([C (ctc->V c)])
                      (cond [(identifier? C) (values #f C)]
                            [else (define xC (fresh-id!))
                                  (values C xC)])))
                  (define guarded-body
                    #`(match/nd: (.Vns → .Ans) (check-C σ #,x #,id-C)
                        [(cons σ (.// (.b #t) _)) #,rest]
                        [(cons σ (.// (.b #f) _))
                         (cons σ (.blm l (quote #,o) #,x #,id-C))]))
                  (cond [compute-C #`(let ([#,id-C #,compute-C]) #,guarded-body)]
                        [else guarded-body])]))
             kont
             xs
             cs)))
  
  ;; Generate code making sure arguments `xs` do NOT match any error conditions `dom`
  ;; Note that this is opposite from `gen-guards`. TODO: better name
  (define/contract (gen-other-guards o xs doms kont-ok)
    (syntax? (listof syntax?) (listof (listof syntax?)) syntax? . -> . syntax?)
    
    (define/contract (gen-other-guards-i xs cs)
      ((listof syntax?) (listof syntax?) . -> . syntax?)
      (with-syntax ([σ (-σ)]
                    [l (-l)])
        (foldr (λ (x c rest)
                 #`(match/nd: (.Vns → .Ans) (check-C σ #,x #,(ctc->V c))
                     [(cons σ (.// (.b #t) _)) #,rest]
                     [(cons σ (.// (.b #f) _)) (cons σ -VsFF)]))
               #`(cons σ (.blm l 'o
                               (→V (.St (.id 'values 'Λ) (list #,@xs)))
                               (→V (.St/C (.id 'values 'Λ) (list #,@(map ctc->V cs))))))
               xs
               cs)))
    
    (with-syntax ([σ (-σ)]
                  [l (-l)])
      (foldr (λ (dom rest)
               #`(match/Ans* #,(gen-other-guards-i xs dom)
                   [(and ans (cons _ (? .blm?))) ans]
                   [_ #,rest]))
             kont-ok
             doms)))
  
  (define/contract (gen-result o xs cs d refinements)
    (syntax? (listof syntax?) (listof syntax?) syntax? (listof syntax?) . -> . syntax?)
    (define-values (concrete-checks unboxed-ids)
      (for/lists (concrete-checks unboxed-ids) ([x (in-list xs)] [c (in-list cs)])
        (check-concrete x c)))
    
    (define wild-cards (datum->syntax o (make-list (length xs) '_)))
    #`(match* #,xs
        [#,concrete-checks (cons #,(-σ) (-Vs (Prim (#,o #,@unboxed-ids))))]
        [#,wild-cards #,(gen-refinements d xs refinements)]))
  
  (define/contract (gen-refinements d xs refinements)
    (syntax? (listof syntax?) (listof syntax?) . -> . syntax?)
    
    ;; Separate contracts that can avoid allocation from other ones
    (define-values (alias-refinements other-refinements)
      (partition
       (λ (refinement)
         (syntax-parse refinement
           [(_ ... (~literal →) d)
            (syntax-parse #'d
              [((~or (~literal =/c) (~literal ≡/c)) v:atom) #t]
              [_ #f])]))
       refinements))
    
    (define alias-refinement-clauses
      (for/list ([refinement (in-list alias-refinements)])
        (syntax-parse refinement
          [(cᵣ ... (~literal →) ((~or (~literal =/c) (~literal ≡/c)) v))
           (define res #`(cons #,(-σ) (-Vs #,(if (identifier? #'v) #'v #'(Prim v)))))
           #`[(and #,@(for/list ([x (in-list xs)]
                                 [c (in-list (syntax->list #'(cᵣ ...)))]
                                 #:unless (syntax-parse c [(~literal any/c) #t] [_ #f]))
                        #`(eq? '✓ (⊢ #,(-σ) #,x #,(ctc->V c)))))
              #,res]])))
    
    (with-syntax ([σ (-σ)])
      #`(cond
          #,@alias-refinement-clauses
          [else
           (let-values ([(σ L) (σ+ σ)])
             (match-define (cons σ′ _) (refine σ L #,(ctc->V d)))
             (set! σ σ′)
             #,@(for/list ([refinement (in-list other-refinements)])
                  (syntax-parse refinement
                    [(cᵣ ... (~literal →) dᵣ)
                     (define refinement-conds
                       (for/list ([x (in-list xs)] [c (in-list (syntax->list #'(cᵣ ...)))])
                         #`(eq? '✓ (⊢ σ #,x #,(ctc->V c)))))
                     #`(when (and #,@refinement-conds)
                         (match-define (cons σ′ _) (refine σ L #,(ctc->V #'dᵣ)))
                         (set! σ σ′))]))
             (cons σ (-Vs L)))])))
  
  (define/contract (check-concrete x c)
    (syntax? syntax? . -> . (values syntax? syntax?))
    
    (define (ctc->pat c)
      (syntax-parse c
        [p?:identifier #`(? p?)]
        [((~literal ¬) d) #`(not #,(ctc->pat #'d))]
        [((~literal ∧) d ...) #`(and #,@(map ctc->pat (syntax->list #'(d ...))))]
        [((~literal ∨) d ...) #`(or #,@(map ctc->pat (syntax->list #'(d ...))))]
        [((~literal >/c) d:real) #`(? (λ (x) (and (real? x) (> x d))))]
        [((~literal ≥/c) d:real) #`(? (λ (x) (and (real? x) (>= x d))))]
        [((~literal </c) d:real) #`(? (λ (x) (and (real? x) (< x d))))]
        [((~literal ≤/c) d:real) #`(? (λ (x) (and (real? x) (<= x d))))]
        [((~literal =/c) d:real) #`(? (λ (x) (and (number? x) (= x d))))]
        [((~literal ♩≠♩/c) d:real) #`(? (λ (x) (and (number? x) (not (= x d)))))]
        [_ (raise-syntax-error 'Internal "don't know how to generate pattern" c)]))
    
    (define id (fresh-id!))
    (values #`(.// (.b (and #,id #,(ctc->pat c))) _) id))
  
  (define/contract (atom->V a)
    (syntax? . -> . syntax?)
    (syntax-parse a
      [x:id #'x]
      [v #'(→V (.b v))]))
  
  (define/contract (o->/C c)
    (syntax? . -> . syntax?)
    (syntax-parse c
      #:literals (+ - * / expt)
      [+ #'+/C]
      [- #'-/C]
      [* #'*/C]
      [/ #'÷/C]
      [expt #'expt/C]
      [remainder #'remainder/C]))
  
  (define/contract (ctc->V c)
    (syntax? . -> . syntax?)
    (syntax-parse c
      [(~literal any/c) #'ANY/C]
      [(~literal number?) #'NUM/C]
      [(~literal real?) #'REAL/C]
      [(~literal integer?) #'INT/C]
      [(~literal boolean?) #'BOOL/C]
      [(~literal symbol?) #'SYM/C]
      [(~literal string?) #'STR/C]
      [(~literal false?) #'FALSE/C]
      [(~or (~literal zero?) ((~literal =/c) 0)) #'ZERO/C]
      [((~literal =/c) 1) #'ONE/C]
      [((~literal ¬) ((~literal =/c) 1)) #'(.¬/C ONE/C)]
      [(~or ((~literal >/c) 0) ((~literal ¬) ((~literal ≤/c) 0))) #'POS/C]
      [(~or ((~literal </c) 0) ((~literal ¬) ((~literal ≥/c) 0))) #'NEG/C]
      [(~or ((~literal ≥/c) 0) ((~literal ¬) ((~literal </c) 0))) #'NON-NEG/C]
      [(~or ((~literal ≤/c) 0) ((~literal ¬) ((~literal >/c) 0))) #'NON-POS/C]
      [(~or ((~literal ¬) (~literal zero?)) ((~literal ¬) ((~literal =/c) 0))) #'NON-ZERO/C]
      [((~literal =/c) (o:o² x y)) #`(#,(o->/C #'o) #,(atom->V #'x) #,(atom->V #'y))]
      [((~literal ¬) ((~literal ¬) c)) (ctc->V #'c)]
      [((~literal ¬) c) #`(.¬/C #,(ctc->V #'c))]
      [((~literal ∧)) #'ANY/C]
      [((~literal ∧) c) (ctc->V #'c)]
      [((~literal ∧) c ... d)
       (foldr (λ (cᵢ C) #`(→V (.St (.id 'and/c 'Λ) (list #,(ctc->V cᵢ) #,C))))
              (ctc->V #'d)
              (syntax->list #'(c ...)))]
      [((~literal ∨)) #'NONE/C]
      [((~literal ∨) c) (ctc->V #'c)]
      [((~literal ∨) c ... d)
       (foldr (λ (cᵢ C) #`(→V (.St (.id 'or/c 'Λ) (list #,(ctc->V cᵢ) #,C))))
              (ctc->V #'d)
              (syntax->list #'(c ...)))]
      [p?:id #'(→V 'p?)]))
  
  (define/contract (fresh-ids n)
    (integer? . -> . (listof identifier?))
    (for/list ([i (in-range n)])

      (datum->syntax #f (string->symbol (format "x~a" i)))))
  
  (define/contract (parse-predicate p? cs)
    (identifier? (listof syntax?) . -> . syntax?)
    (define xs (fresh-ids (length cs)))
    (with-syntax ([p? p?])
      #`(('p? (list #,@xs))
         #,(gen-guards #'p? xs cs
                       (match xs
                         [(list x) #`(match/nd: (.Vns → .Vnss) (check-C #,(-σ) #,x #,(ctc->V #'p?))
                                       [(cons σ V) (cons σ (-Vs V))])]
                         [(list x y) #`(match/nd: (.Vns → .Vnss) (check-o² #,(-σ) 'p? #,x #,y)
                                         [(cons σ V) (cons σ (-Vs V))])]
                         [_ (raise-syntax-error
                             'Internal
                             "only support unary and binary predicates for now")])))))
  
  (define/contract (parse-clause clause)
    (syntax? . -> . syntax?)
    
    (syntax-parse clause
      ;; Main cases
      [[#:escape (o:expr args:expr) body:expr ...]
       #'[(o args) body ...]]
      [[dec:decl #:other-errors domₑ:dom ... #:refinements sigᵣ:sig ...]
       (parse-arith #'dec (syntax->list #'(domₑ ...)) (syntax->list #'(sigᵣ ...)))]
      [[#:predicate p?:id : c ...]
       (parse-predicate #'p? (syntax->list #'(c ...)))]
      ;; Shorthand cases
      [[dec:decl]
       (parse-clause #'[dec #:other-errors #:refinements])]
      [[dec:decl #:other-errors (dom:ctc ...) ...]
       (parse-clause #'[dec #:other-errors (dom ...) ... #:refinements])]
      [[dec:decl #:refinements refinements:sig ...]
       (parse-clause #'[dec #:other-errors #:refinements refinements ...])]
      [[#:predicate p?:id]
       (parse-clause #'[#:predicate p? : any/c])])))

(define-syntax (define-δ stx)
  (syntax-parse stx
    [(define-δ clause:δ-clause ...)
     (with-syntax ([σ (datum->syntax stx 'σ)]
                   [l (datum->syntax stx 'l)]
                   [o (datum->syntax stx 'o)]
                   [Vs (datum->syntax stx 'Vs)]
                   [δ (datum->syntax stx 'δ)])
       (define parsed-clauses
         (parameterize ([-σ #'σ] [-l #'l])
           (map parse-clause (syntax->list #'(clause ...)))))
       (define ans
         #`(begin
             (: δ : .σ .o (Listof .V) Mon-Party → .Ans*)
             (define (δ σ o Vs l)
               ;(printf "δ⟦~a, ~a⟧~n" (name o) Vs)
               (match* (o Vs)
                 #,@parsed-clauses
                    [(⋆ Vs)
                     (cons σ (.blm l (name ⋆) (Prim (length Vs)) (arity=/C -1 #|hack|#)))]))))
       (pretty-print (syntax->datum ans))
       ans)]))
