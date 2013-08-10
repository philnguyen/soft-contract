#lang racket
(require "lang.rkt" "prim.rkt" "syntax.rkt" "show.rkt")
(provide #;(combine-out Δ refine)
         (contract-out
          [Δ (l? σ? o? [listof V?] . -> . (nd/c (cons/c σ? A?)))]
          [refine (((cons/c σ? V?)) () #:rest (listof (nd/c C?)) . ->* . (cons/c σ? V?))]))

(define (Δ l σ o Vs)
  #;(debug "~a ~a~n~n" o (map show-E Vs))
  (match* (o Vs)
    
    ; total predicates
    [([? total-pred? p] `[,V]) (check-p σ V p)]
    
    ; accessors
    [([struct-ac t _ i] `[,(val [Struct t Vs] _)]) (cons σ (list-ref Vs i))]
    [([struct-ac t n i] `[,V])
     (match/nd (Δ 'Δ σ [struct-p t n] Vs)
       ; not struct but can be struct -> must be label
       [(cons σ1 (val #t _))
        (match V
          [(? L? L) (match (σ@ σ1 L)
                      [(val (Struct t Vs) _) (cons σ1 (list-ref Vs i))]
                      [_ (cons σ1 ★)])]
          [(val (•) Cs) (cons σ1 ★)])]
       [(cons σ1 (val #f _))
        (cons σ1 (bl l t "Access ~a field of ~a ~a, given ~a"
                     (ord (add1 i)) (artcl t) t (show-E (σ@* σ1 V))))])]
    
    ; arithmetics
    [([op '=] `[,V1 ,V2])
     (match/nd (Δ 'Δ σ [op 'num?] `[,V1])
       [(cons σ1 (val #t _))
        (match/nd (Δ 'Δ σ1 [op 'num?] `[,V2])
          [(cons σ2 (val #t _)) (δ σ2 '= Vs)]
          [(cons σ2 (val #f _)) (cons σ2 [bl l '= "Expect num?, given ~a" (show-E (σ@* σ2 V2))])])]
       [(cons σ1 (val #f _)) (cons σ1 [bl l '= "Expect num?, given ~a" (show-E (σ@* σ1 V1))])])]
    [([op (and name (or 'add1 'sub1))] `[,_])
     (match/nd (Δ 'Δ σ [op 'num?] Vs)
       [(cons σ1 (val #t _)) (δ σ1 name Vs)]
       [(cons σ1 (val #f _)) (cons σ1 [bl l name "Expect num?, given ~a" (show-E (σ@* σ1 (first Vs)))])])]
    [([op (and name (or '+ '- '* '≠))] `[,V1 ,V2])
     (match/nd (Δ 'Δ σ [op 'num?] `[,V1])
       [(cons σ1 (val #t _))
        (match/nd (Δ 'Δ σ1 [op 'num?] `[,V2])
          [(cons σ2 (val #t _)) (δ σ2 name Vs)]
          [(cons σ2 (val #f _)) (cons σ2 [bl l name "Expect num?, given ~a" (show-E (σ@* σ2 V2))])])]
       [(cons σ1 (val #f _)) (cons σ1 [bl l name "Expect num?, given ~a" (show-E (σ@* σ1 V1))])])]
    [([op '/] `[,V1 ,V2])
     (match/nd (Δ 'Δ σ [op 'num?] `[,V1])
       [(cons σ1 (val #t _))
        (match/nd (Δ 'Δ σ1 [op 'num?] `[,V2])
          [(cons σ2 [val #t _])
           (match/nd (Δ 'Δ σ2 [op '=] (list V2 ZERO))
             [(cons σ3 [val #t _]) (cons σ3 [bl l '/ "Div by 0"])]
             [(cons σ3 [val #f _]) (δ σ3 '/ Vs)]
             [_ ∅])]  ; ignore error from zero?
          [(cons σ2 [val #f _]) (cons σ2 [bl l '/ "Expect non-0 number, given ~a" (show-E (σ@* σ2 V2))])])]
       [(cons σ1 (val #f _)) (cons σ1 [bl l '/ "Expect num?, given ~a" (show-E (σ@* σ1 V1))])])]
    [([op (and name (or '> '< '<= '≤ '>= '≥))] `[,V1 ,V2])
     (match/nd (Δ 'Δ σ [op 'real?] `[,V1])
       [(cons σ1 (val #t _))
        (match/nd (Δ 'Δ σ1 [op 'real?] `[,V2])
          [(cons σ2 (val #t _)) (δ σ2 name Vs)]
          [(cons σ2 (val #f _)) (cons σ2 [bl l name "Expect real?, given ~a" (show-E (σ@* σ2 V2))])])]
       [(cons σ1 (val #f _)) (cons σ1 [bl l name "Expect real?, given ~a" (show-E (σ@* σ1 V1))])])]
    [([op 'str-len] `[,_])
     (match/nd (Δ 'Δ σ [op 'str?] Vs)
       [(cons σ1 (val #t _)) (δ σ1 'str-len Vs)]
       [(cons σ1 (val #f _)) (cons σ1 [bl l 'str-len "Expect str?, given ~a" (show-E (σ@* σ1 (first Vs)))])])]
    [([op 'equal?] `[,V1 ,V2]) (V-equal? σ V1 V2)]
    
    ;; constructor
    [([struct-mk t n] _) (if (= (length Vs) n)
                             (cons σ [val (Struct t Vs) ∅])
                             (cons σ [bl l t "Constructor ~a expects ~a fields, given ~a" t n (length Vs)]))]
    
    ;; anything else is an error
    [([struct-ac t _ _] _) (cons σ [bl l t "Illegal use of accessor ~a" t])]
    [([op name] _) (cons σ [bl l name "Illegal use of operator ~a" name])]))

;; maps op name and (assumed valid) arguments to answer value
(define/contract (δ σ o Vs)
  (σ? o-name? (listof V?) . -> . (nd/c (cons/c σ? V?)))
  (match* (o Vs)
    [('add1 (list V)) (δ σ '+ (list V ONE))]
    [('sub1 (list V)) (δ σ '- (list V ONE))]
    
    [('* (list V1 V2))
     ; Ws are most looked-up, Xs are most looked-up without sacrificing precision
     (match (map (curry σ@* σ) Vs)
       [(list (val (? number? m) _) (val (? number? n) _)) (cons σ (val (* m n) ∅))]
       [(list (and W1 (val U1 _)) (and W2 (val U2 _)))
        (let ([X1 (if (number? U1) W1 V1)]
              [X2 (if (number? U2) W2 V2)])
          (cond
            [(equal? 'Proved (prove? σ X1 ZERO/C)) (cons σ ZERO)]
            [(equal? 'Proved (prove? σ X2 ZERO/C)) (cons σ ZERO)]
            [(equal? 'Proved (prove? σ X1 ONE/C)) (cons σ X2)]
            [(equal? 'Proved (prove? σ X2 ONE/C)) (cons σ X1)]
            [else
             (refine (σ+ σ)
                     (cond ; preserve class
                       [(all-prove? σ Vs INT/C) INT/C]
                       [(all-prove? σ Vs REAL/C) REAL/C]
                       [else NUM/C])
                     (prd/C X1 X2))]))])]
    [('/ (list V1 V2))
     ; Ws are most looked-up, Xs are most looked-up without sacrificing precision
     (match (map (curry σ@* σ) Vs)
       [(list (val (? number? m) _) (val (? number? n) _)) (cons σ (val (/ m n) ∅))]
       [(list (and W1 (val U1 _)) (and W2 (val U2 _)))
        (let ([X1 (if (number? U1) W1 V1)]
              [X2 (if (number? U2) W2 V2)])
          (cond
            [(equal? 'Proved (prove? σ X1 ZERO/C)) (cons σ ZERO)]
            [else (refine (σ+ σ)
                          (cond ; preserve class
                            [(all-prove? σ Vs REAL/C) REAL/C]
                            [else NUM/C])
                          (rat/C X1 X2))]))])]
    [('+ (list V1 V2))
     ; Ws are most looked-up, Xs are most looked-up without sacrificing precision
     (match (map (curry σ@* σ) Vs)
       [(list (val (? number? m) _) (val (? number? n) _)) (cons σ (val (+ m n) ∅))]
       [(list (and W1 (val U1 _)) (and W2 (val U2 _)))
        (let ([X1 (if (number? U1) W1 V1)]
              [X2 (if (number? U2) W2 V2)])
          (cond
            [(equal? 'Proved (prove? σ X1 ZERO/C)) (cons σ X2)]
            [(equal? 'Proved (prove? σ X2 ZERO/C)) (cons σ X1)]
            [else (refine (σ+ σ)
                          (cond ; preserve class
                            [(all-prove? σ Vs INT/C) INT/C]
                            [(all-prove? σ Vs REAL/C) REAL/C]
                            [else NUM/C])
                          (sum/C X1 X2))]))])]
    [('- (list V1 V2))
     ; Ws are most looked-up, Xs are most looked-up without sacrificing precision
     (match (map (curry σ@* σ) Vs)
       [(list (val (? number? m) _) (val (? number? n) _)) (cons σ (val (- m n) ∅))]
       [(list (and W1 (val U1 _)) (and W2 (val U2 _)))
        (let ([X1 (if (number? U1) W1 V1)]
              [X2 (if (number? U2) W2 V2)])
          (cond
            [(equal? 'Proved (prove? σ X2 ZERO/C)) (cons σ X1)]
            [else (refine (σ+ σ)
                          (cond ; preserve class
                            [(all-prove? σ Vs INT/C) INT/C]
                            [(all-prove? σ Vs REAL/C) REAL/C]
                            [else NUM/C])
                          (dif/C X1 X2))]))])]
    
    [('str-len (list V))
     (match (σ@* σ V)
       [(val (? string? s) _) (cons σ (val (string-length s) ∅))]
       [_ (refine (σ+ σ) INT/C NON-NEG/C)] #|TODO improve|#)]
    [('= `(,V1 ,V2))
     #;(debug "-- ~a ~a~n~n" (show-E V1) (show-E V2))
     ; Ws are most looked-up, Xs are most looked-up without sacrificing precision
     (match (map (curry σ@* σ) Vs)
       [(list (val (? number? m) _) (val (? number? n) _)) (cons σ (val (= m n) ∅))]
       [(list (and W1 (val U1 _)) (and W2 (val U2 _)))
        (let ([X1 (if (number? U1) W1 V1)]
              [X2 (if (number? U2) W2 V2)])
          (match (prove? σ X1 (=/C X2))
            ['Proved (cons σ TT)]
            ['Refuted (cons σ FF)]
            ['Neither
             (match (prove? σ X2 (=/C X1))
               ['Proved (cons σ TT)]
               ['Refuted (cons σ FF)]
               ['Neither
                (match-let* ([(cons σT _) (refine1 (cons σ V1) (=/C X2))]
                             [(cons σT _) (refine1 (cons σT V2) (=/C X1))]
                             [(cons σF _) (refine1 (cons σ V1) (≠/C X2))]
                             [(cons σF _) (refine1 (cons σF V2) (≠/C X1))])
                  {set (cons σT TT) (cons σF FF)})])]))])]
    [('< (list V1 V2))
     ; Ws are most looked-up, Xs are most looked-up without sacrificing precision
     (match (map (curry σ@* σ) Vs)
       [(list (val (? number? m) _) (val (? number? n) _)) (cons σ (val (< m n) ∅))]
       [(list (and W1 (val U1 _)) (and W2 (val U2 _)))
        (let ([X1 (if (number? U1) W1 V1)]
              [X2 (if (number? U2) W2 V2)])
          (match (prove? σ X1 (</C X2))
            ['Proved (cons σ TT)]
            ['Refuted (cons σ FF)]
            ['Neither
             (match (prove? σ X2 (>/C X1))
               ['Proved (cons σ TT)]
               ['Refuted (cons σ FF)]
               ['Neither
                (match-let* ([(cons σT _) (refine1 (cons σ V1) (</C X2))]
                             [(cons σT _) (refine1 (cons σT V2) (>/C X1))]
                             [(cons σF _) (refine1 (cons σ V1) (≥/C X2))]
                             [(cons σF _) (refine1 (cons σF V2) (≤/C X1))])
                  {set (cons σT TT) (cons σF FF)})])]))])]
    [('> (list V1 V2)) (δ σ '< (list V2 V1))]
    [('>= (list V1 V2)) (match/nd (δ σ '< (list V1 V2))
                          [(cons σ1 (val #t _)) (cons σ1 FF)]
                          [(cons σ1 (val #f _)) (cons σ1 TT)])]
    [('<= (list V1 V2)) (δ σ '>= (list V2 V1))]))

(define (V-equal? σ V1 V2)
  (match* (V1 V2)
    [([? L? l] [? L? l]) (cons σ TT)]
    [([? L? l] [not (? opaque?)])
     (match/nd (V-equal? σ [σ@ σ l] V2)
       [(cons σ [val #t _]) (cons [σ-set σ l V2] TT)]
       [a a])]
    [([not (? opaque?)] [? L? l])
     (match/nd (V-equal? σ V1 [σ@ σ l])
       [(cons σ [val #t _]) (cons [σ-set σ l V1] TT)]
       [a a])]
    [(_ [? L? l]) (V-equal? σ V1 [σ@ σ l])]
    [([? L? l] _) (V-equal? σ [σ@ σ l] V2)]
    [(_ [val (•) _]) {set (cons σ TT) (cons σ FF)}]
    [([val (•) _] _) {set (cons σ TT) (cons σ FF)}]
    [([val (Struct t1 Vs1) _] [val (Struct t2 Vs2) _])
     (if (equal? t1 t2)
         (let loop ([σ σ] [Vs1 Vs1] [Vs2 Vs2])
           (match* (Vs1 Vs2)
             [('() '()) (cons σ TT)]
             [([cons V1 Vr1] [cons V2 Vr2])
              (match/nd (V-equal? σ V1 V2)
                [(cons σ1 [val #t _]) (loop σ1 Vr1 Vr2)]
                [a a])]))
         (cons σ FF))]
    [([val u1 _] (val u2 _)) (cons σ (val (equal? u1 u2) ∅))]))

;; checks whether value satisfies predicate
(define (check-p σ V p)
  (match (prove? σ V [close p ρ∅])
    ['Proved (cons σ TT)]
    ['Refuted (cons σ FF)]
    ['Neither (match-let ([(cons σ1 _) (refine1 (cons σ V) (close p ρ∅))]
                          [(cons σ2 _) (refine1 (cons σ V) (close (¬ p) ρ∅))])
                {set (cons σ1 TT) (cons σ2 FF)})]))

(define (refine σV . C*)
  (for/fold ([σV σV]) ([C C*])
    (if (C? C) (refine1 σV C)
        (for/fold ([σV σV]) ([Ci C]) (refine1 σV Ci)))))

(define (refine* σ Vs cs ρ)
  (let-values ([(σ1 Vs-rev)
                (for/fold ([σi σ] [V* '()]) ([Vi Vs] [ci cs])
                  (match-let ([(cons σj Vj) (refine (cons σi Vi) (close ci ρ))])
                    (values σj (cons Vj V*))))])
    (cons σ1 (reverse Vs-rev))))

(define (refine1 σV C)
  (let ([C (simplify-C C)])
    (match-let ([(close c ρ) C]
                [(cons σ V) σV])
      (match (prove? σ V C)
        ['Proved σV]
        ['Refuted (error (format "refine: Value definitely refutes contract;~nValue: ~a~nContract:~a~n" (show-E V) (show-C C)))]
        ['Neither
         (match* (V c)
           [(_ [and-c c1 c2]) (refine1 (refine1 σV [close c1 ρ]) [close c2 ρ])]
           [(_ [or-c c1 c2]) ; we used to split here. But let's be lazy now...
            (let ([C1 (close c1 ρ)]
                  [C2 (close c2 ρ)])
              (match* ([prove? σ V C1] [prove? σ V C2])
                [('Refuted 'Refuted) (printf "C1: ~a~nC2:~a~n" C1 C2) (error "WTF??")]
                [(_ 'Refuted) (refine1 σV C1)]
                [('Refuted _) (refine1 σV C2)]
                [(_ _) (match V ; existing refinements can prune off one branch
                         [(val u Cs) (cons σ (val u [intersect-Cs σ Cs C]))]
                         [(? L? l) (match-let* ([(val u Cs) (σ@ σ l)]
                                                [V′ (val u [intersect-Cs σ Cs C])])
                                     (cons [σ-set σ l V′] l))])]))]
           [(_ [μ-c x c1]) (refine1 σV [close (subst/c c1 x c) ρ])] ; FIXME no need?
           
           [((val (•) Cs) (f 1 (@ _ (op (or 'equal? '=)) (list (x 0) e)) #f))
            (match e
              [(? b? b) (cons σ (val b Cs))]
              [(and (? f? f) (? closed?)) (val (close f ρ∅) Cs)]
              [(x sd) (match-let ([V1 (σ@* σ (ρ@ ρ (- sd 1)))])
                        (refine (cons σ V1) Cs))]
              [_ (cons σ (val (•) (set-add Cs C)))])]
           
           ; struct contracts
           [((val (Struct t Vs) Cs) (struct-c t cs))
            (match-let ([(cons σ1 Vs) (refine* σ Vs cs ρ)])
              (cons σ1 (val (Struct t Vs) Cs)))]
           [((val (•) Cs) (struct-c t cs))
            (match-let ([(cons σ1 Ls) (σ++ σ (length cs))])
              (refine1 (cons σ1 (val (Struct t Ls) Cs)) C))]
           [((val (•) Cs) (struct-p t n))
            (match-let* ([(cons σ1 Ls) (σ++ σ n)]
                         [V1 (val (Struct t Ls) Cs)])
              ; might be useful to redistribute contracts in current refinement set
              (for/fold ([σV (cons σ1 V1)]) ([C Cs])
                (refine1 σV C)))]
           [((? L? L) _) (match-let ([(cons σ1 V1) (refine1 (cons σ (σ@ σ L)) C)])
                           (cons (σ-set σ1 L V1) L))]
           
           ; rematerialize for singleton predicates
           [([val u Cs] [op (and p (or 'false? 'true?))])
            (cons σ [val (match p ['false? #f] ['true? #t]) Cs])]
           
           [([val u Cs] _)
            (match-let*
                ([Cs1 (intersect-Cs σ Cs C)]
                 [Ck (for/or ([Ci Cs1]
                              #:when
                              (match? Ci (close (or (? struct-c?) (? struct-p?)) _)))
                       Ci)]
                 [(cons σ2 u′)
                  (match Ck
                    [#f (cons σ u)]
                    [(close (struct-p t n) _)
                     (match-let ([(cons σ1 Ls) (σ++ σ n)])
                       (cons σ1 (Struct t Ls)))]
                    [(close (struct-c t cs) ρc)
                     (match-let ([(cons σ1 Ls) (σ++ σ (length cs))])
                       (cons
                        (let loop ([σi σ1] [Ls Ls] [cs cs])
                          (match* (Ls cs)
                            [('() '()) σi]
                            [([cons Li Ls′] [cons ci cs′])
                             (match-let ([(cons σ′ _) (refine1 (cons σi Li) (close ci ρc))])
                               (loop σ′ Ls′ cs′))]))
                        (Struct t Ls)))])]
                 [Cs2 (match Ck
                        [#f Cs1]
                        [(and Ck (close _ _)) (set-remove Cs1 Ck)])])
              (cons σ2 (val u′ Cs2)))])]))))

(define (intersect-Cs σ Cs Cn)
  (if (set-empty? Cs) {set Cn}
      (for/fold ([acc ∅]) ([Ci (in-set Cs)])
        (∪ acc (intersect-C σ Ci Cn)))))

(define (intersect-C σ C D)
  (define go (curry intersect-C σ))
  (cond
    [(equal? 'Proved (C-prove? σ C D)) C]
    [(equal? 'Proved (C-prove? σ D C)) D]
    [else
     (match-let ([(close c ρc) C]
                 [(close d ρd) D])
       (match* (c d)
         ; unroll recursive ones
         [(_ (μ-c x d1)) (go C (close (subst/c d1 x d) ρd))]
         [((μ-c x c1) _) (go (close (subst/c c1 x c) ρc) D)]
         ; break conjunctive ones
         [(_ (and-c d1 d2)) (set-union (go C (close d1 ρd)) (go C (close d2 ρd)))]
         [((and-c c1 c2) _) (set-union (go (close c1 ρc) D) (go (close c2 ρc) D))]
         ; prune stuff in disjunctive ones if possible
         [(_ (? or-c?)) (let ([D′ (truncate σ D C)])
                          (if (equal? D D′) {set C D} (go C D′)))]
         [((? or-c?) _) (let ([C′ (truncate σ C D)])
                          (if (equal? C C′) {set C D} (go C′ D)))]
         ; special rules for contracts on reals
         [((f 1 (@ l (op '>=) (list e1 e2)) #f)
           (f 1 (@ _ (op 'false?)
                   (list (@ _ (op (or '= 'equal?)) (or (list e1 e2) (list e2 e1))))) #f))
          (if (equal? ρc ρd)
              (close (f 1 (@ l (op '>) (list e1 e2)) #f) ρc)
              {set C D})]
         [((f 1 (@ _ (op 'false?)
                   (list (@ _ (op (or '= 'equal?)) (or (list e1 e2) (list e2 e1))))) #f)
           (f 1 (@ l (op '>=) (list e1 e2)) #f))
          (if (equal? ρc ρd)
              (close (f 1 (@ l (op '>) (list e1 e2)) #f) ρd)
              {set C D})]
         [((f 1 (@ l (op '<=) (list e1 e2)) #f)
           (f 1 (@ _ (op 'false?)
                   (list (@ _ (op (or '= 'equal?)) (or (list e1 e2) (list e2 e1))))) #f))
          (if (equal? ρc ρd)
              (close (f 1 (@ l (op '<) (list e1 e2)) #f) ρc)
              {set C D})]
         [((f 1 (@ _ (op 'false?)
                   (list (@ _ (op (or '= 'equal?)) (or (list e1 e2) (list e2 e1))))) #f)
           (f 1 (@ l (op '<=) (list e1 e2)) #f))
          (if (equal? ρc ρd)
              (close (f 1 (@ l (op '<) (list e1 e2)) #f) ρd)
              {set C D})]
         [(_ _) {set C D}]))]))

; prunes off all branches of disjunction that are excluded by given contract
(define (truncate σ C D)
  (define go (curry truncate σ))
  (match-let ([(close c ρc) C]
              [(close d ρd) D])
    (match c
      [(or-c c1 c2)
       (let ([C1 (close c1 ρc)]
             [C2 (close c2 ρc)])
         (match* ([C-prove? σ D C1] [C-prove? σ D C2])
           [('Refuted 'Refuted) (error "WTF??")]
           [(_ 'Refuted) (go C1 D)]
           [('Refuted _) (go C2 D)]
           [(_ _) (match-let ([(close c1p _) (go C1 D)]
                              [(close c2p _) (go C2 D)])
                    (close (or-c c1p c2p) ρc))]))]
      [_ C])))

(define (¬ v)
  (f 1 (@ 'Δ [op 'false?] [list (@ 'Δ v [list (x 0)])]) #f))

(define (ord k)
  (format "~a~a" k
          (match k
            [(or 11 12 13) 'th]
            [_ (match (remainder k 10) [1 'st] [2 'nd] [3 'rd] [_ 'th])])))

(define/match (artcl w)
  [((? symbol? s)) (artcl (symbol->string w))]
  [((regexp #rx"^(a|e|i|o|u)")) 'an]
  [(_) 'a])

(define (min/max a b)
  (if (<= a b) (values a b) (values b a)))