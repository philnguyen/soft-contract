#lang typed/racket/base
(provide (all-defined-out))

(require
 racket/match racket/list racket/set racket/function racket/bool racket/math
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
     (if (equal? t1 t2)
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

(: check-C : .σ .V .V → .Vns*)
(define (check-C σ V C)
  (match (⊢ σ V C)
    ['✓ (cons σ TT)]
    ['X (cons σ FF)]
    ['?
     (define-values (σt _t) (refine σ V C))
     (define-values (σf _f) (refine σ V (.¬/C C)))
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
        (define-values (σt _t)
          (match* (X₁ X₂)
            [((.L i) (.L j))
             (if (> i j) (refine σ X₁ C₂) (refine σ X₂ C₁))]
            [((? .L?) _) (refine σ X₁ C₂)]
            [(_ (? .L?)) (refine σ X₂ C₁)]
            [(_ _) (values σ 'ignore)]))
        (define-values (σf _f)
          (match* (X₁ X₂)
            [((.L i) (.L j))
             (if (> i j) (refine σ X₁ (.¬/C C₂)) (refine σ X₂ (.¬/C C₁)))]
            [((? .L?) _) (refine σ X₁ (.¬/C C₂))]
            [(_ (? .L?)) (refine σ X₂ (.¬/C C₁))]
            [(_ _) (values σ 'ignore)]))
        {set (cons σt TT) (cons σf FF)}])]))

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
             (define-values (σ′ _) (refine σ L #,(ctc->V d)))
             (set! σ σ′)
             #,@(for/list ([refinement (in-list other-refinements)])
                  (syntax-parse refinement
                    [(cᵣ ... (~literal →) dᵣ)
                     (define refinement-conds
                       (for/list ([x (in-list xs)] [c (in-list (syntax->list #'(cᵣ ...)))])
                         #`(eq? '✓ (⊢ σ #,x #,(ctc->V c)))))
                     #`(when (and #,@refinement-conds)
                         (define-values (σ′ _) (refine σ L #,(ctc->V #'dᵣ)))
                         (set! σ σ′))]))
             (cons σ (-Vs L)))])))
  
  (define/contract (check-concrete x c)
    (syntax? syntax? . -> . (values syntax? syntax?))
    
    (define (ctc->pat c)
      (syntax-parse c
        [p?:identifier (datum->syntax #'p? (list '? #'p?))]
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
    (cond
      [(identifier? c) ; more precise when [L ↦ concrete]
       (values #`(or (.// (.b (? #,c #,id)) _)
                     (and (.L _) (app (curry σ@ #,(-σ)) (.// (.b (? #,c #,id)) _))))
               #`(assert #,id #,c))]
      [else
       (define -c (ctc->pat c))
       (values #`(.// (.b (and #,id #,-c)) _) id)]))
  
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
