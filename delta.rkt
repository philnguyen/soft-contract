#lang racket
(require "lang.rkt" "prim.rkt" "syntax.rkt")
(provide (combine-out Δ refine)
         #;(contract-out
            [Δ (l? σ? o? [listof V?] . -> . (nd/c (cons/c σ? A?)))]
            [refine ((cons/c σ? V?) C? . -> . (cons/c σ? V?))]))

(define TT (val #t ∅))
(define FF (val #f ∅))

(define (Δ l σ o Vs)
  (match* (o Vs)
    
    ; total predicates
    [([? total-pred? p] `[,V]) (check-p σ V p)]
    
    ; partial predicates
    [([op 'zero?] `[,V])
     (match/nd (Δ 'Δ σ [op 'num?] Vs)
       [(cons σ1 (val #t _)) (check-p σ1 V [op 'zero?])]
       [(cons σ1 (val #f _)) (cons σ1 (Blm l 'zero?))])]
    [([op (and name [or 'positive? 'negative?])] `[,V])
     (match/nd (Δ 'Δ σ [op 'real?] Vs)
       [(cons σ1 (val #t _)) (check-p σ1 V [op name])]
       [(cons σ1 (val #f _)) (cons σ1 (Blm l name))])]
    
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
       [(cons σ1 (val #f _)) (cons σ1 (Blm l t))])]
    
    ; arithmetics
    [([op '=] `[,V1 ,V2])
     (match/nd (Δ 'Δ σ [op 'num?] `[,V1])
       [(cons σ1 (val #t _))
        (match/nd (Δ 'Δ σ1 [op 'num?] `[,V2])
          [(cons σ2 (val #t _)) (Δ 'Δ σ2 [op 'equal?] `[,V1 ,V2])]
          [(cons σ2 (val #f _)) (cons σ2 [Blm l '=])])]
       [(cons σ1 (val #f _)) (cons σ1 [Blm l '=])])]
    [([op (and name (or 'add1 'sub1))] `[,_])
     (match/nd (Δ 'Δ σ [op 'num?] Vs)
       [(cons σ1 (val #t _)) (cons σ1 [δ name (map [curry σ@* σ1] Vs)])]
       [(cons σ1 (val #f _)) (cons σ1 [Blm l name])])]
    [([op (and name (or '+ '- '* '≠))] `[,V1 ,V2])
     (match/nd (Δ 'Δ σ [op 'num?] `[,V1])
       [(cons σ1 (val #t _))
        (match/nd (Δ 'Δ σ1 [op 'num?] `[,V2])
          [(cons σ2 (val #t _)) (cons σ2 [δ name (map [curry σ@* σ2] Vs)])]
          [(cons σ2 (val #f _)) (cons σ2 [Blm l name])])]
       [(cons σ1 (val #f _)) (cons σ1 [Blm l name])])]
    [([op '/] `[,V1 ,V2])
     (match/nd (Δ 'Δ σ [op 'num?] `[,V1])
       [(cons σ1 (val #t _))
        (match/nd (Δ 'Δ σ1 [op 'num?] `[,V2])
          [(cons σ2 [val #t _])
           (match/nd
               (Δ 'Δ σ2 [op 'zero?] `[,V2])
             [(cons σ3 [val #t _]) (cons σ3 [Blm l '/])]
             [(cons σ3 [val #f _]) (cons σ3 [δ '/ (map [curry σ@* σ3] Vs)])]
             [_ ∅])]  ; ignore error from zero?
          [(cons σ2 [val #f _]) (cons σ2 [Blm l '/])])]
       [(cons σ1 (val #f _)) (cons σ1 [Blm l '/])])]
    [([op (and name (or '> '< '<= '≤ '>= '≥))] `[,V1 ,V2])
     (match/nd (Δ 'Δ σ [op 'real?] `[,V1])
       [(cons σ1 (val #t _))
        (match/nd (Δ 'Δ σ1 [op 'real?] `[,V2])
          [(cons σ2 (val #t _)) (match/nd (δ name (map (curry σ@* σ2) Vs))
                                  [A (cons σ2 A)])]
          [(cons σ2 (val #f _)) (cons σ2 [Blm l name])])]
       [(cons σ1 (val #f _)) (cons σ1 [Blm l name])])]
    [([op 'str-len] `[,_])
     (match/nd (Δ 'Δ σ [op 'str?] Vs)
       [(cons σ1 (val #t _)) (cons σ1 [δ 'str-len (map [curry σ@* σ1] Vs)])]
       [(cons σ1 (val #f _)) (cons σ1 [Blm l 'str-len])])]
    [([op 'equal?] `[,V1 ,V2]) (V-equal? σ V1 V2)]
    
    ;; constructor
    [([struct-mk t n] _) (if (= (length Vs) n)
                             (cons σ [val (Struct t Vs) ∅])
                             (cons σ [Blm l t]))]
    
    ;; anything else is an error
    [([struct-ac t _ _] _) (cons σ [Blm l t])]
    [([op name] _) (cons σ [Blm l name])]))

;; maps op name and (assumed valid) arguments to answer value
(define/match (δ o Vs)
  ; concrete, precise values
  [('add1 `(,[val (? number? x) _])) (val (add1 x) ∅)]
  [('sub1 `(,[val (? number? x) _])) (val (sub1 x) ∅)]
  [([and name (or '+ '- '* '/ '≠)] `(,[val (? number? x) _] ,[val (? number? y) _]))
   (val ((match name ['+ +] ['- -] ['* *] ['/ /]) x y) ∅)]
  [([and name (or '> '< '>= '<=)] `(,[val (? real? x) _] ,[val (? real? y) _]))
   (val ((match name ['< <] ['> >] ['>= >=] ['<= <=]) x y) ∅)]
  [('str-len `(,[val (? string? x) _])) (val (string-length x) ∅)]
  
  ; semi-precise values
  [('* (or `(,[val 0 _] ,_) `(,_ ,[val 0 _]))) (val 0 ∅)]
  [('/ `(,[val 0 _] ,_)) (val 0 ∅)]
  [('/ `(,[val (? number?) _] ,_))
   (val (•) {set (close [op 'num?] ρ∅) (close [¬ (op 'zero?)] ρ∅)})]
  [('/ Vs)
   (val (•) {set (close
                  (op (if (all-prove? σ∅ Vs (close (op 'real?) ρ∅)) 'real? 'num?))
                  ρ∅)})]
  [([or '+ 'add1] Vs)
   (val (•)
        (∪ ∅
           (cond ; try to preserve int/real-ness
             [(all-prove? σ∅ Vs (close (op 'int?) ρ∅)) (close (op 'int?) ρ∅)]
             [(all-prove? σ∅ Vs (close (op 'real?) ρ∅)) (close (op 'real?) ρ∅)]
             [else (close (op 'num?) ρ∅)])
           (cond ; try to preserve sign
             [(all-prove? σ∅ Vs (close (op 'zero?) ρ∅)) (close (op 'zero?) ρ∅)]
             [(all-prove? σ∅ Vs (close (or-c (op 'zero?) (op 'positive?)) ρ∅))
              (if (some-proves? σ∅ Vs (close (op 'positive?) ρ∅))
                  (close (op 'positive?) ρ∅)
                  (close (or-c (op 'zero?) (op 'positive?)) ρ∅))]
             [(all-prove? σ∅ Vs (close (or-c (op 'zero?) (op 'negative?)) ρ∅))
              (if (some-proves? σ∅ Vs (close (op 'negative?) ρ∅))
                  (close (op 'negative?) ρ∅)
                  (close (or-c (op 'zero?) (op 'negative?)) ρ∅))]
             [else ∅])))]
  [([or '- '* 'sub1] Vs)
   (val (•)
        {set (close (op (cond
                          [(all-prove? σ∅ Vs (close (op 'int?) ρ∅)) 'int?]
                          [(all-prove? σ∅ Vs (close (op 'real?) ρ∅)) 'real?]
                          [else 'num?]))
                    ρ∅)})]
  
  ; abstract result...
  [('str-len _) (val (•) {set (close [op 'int?] ρ∅)})]
  [([or '> '< '>= '<=] _) {set TT FF}])

(define (V-equal? σ V1 V2)
  (match* (V1 V2)
    [([? L? l] [? L? l]) (cons σ [val #t ∅])]
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
             [([cons V1 Vs1] [cons V2 Vs2])
              (match/nd (V-equal? σ V1 V2)
                [(cons σ1 [val #t _]) (loop σ1 Vs1 Vs2)]
                [a a])]))
         (cons σ FF))]
    [([val u1 _] (val u2 _)) (cons σ (val (equal? u1 u2) ∅))]))

;; checks whether value satisfies predicate
(define (check-p σ V p)
  (match (prove? σ V [close p ρ∅])
    ['Proved (cons σ TT)]
    ['Refuted (cons σ FF)]
    ['Neither (match-let ([(cons σ1 _) (refine (cons σ V) (close p ρ∅))]
                          [(cons σ2 _) (refine (cons σ V) (close (¬ p) ρ∅))])
                {set (cons σ1 TT) (cons σ2 FF)})]))

(define (refine σV C)
  (match-let ([(close c ρ) C]
              [(cons σ V) σV])
    (match* (V c)
      [(_ [op 'any]) σV]
      [(_ [and-c c1 c2]) (refine (refine σV [close c1 ρ]) [close c2 ρ])]
      [(_ [or-c c1 c2]) ; we used to split here. But let's be lazy now...
       (let ([C1 (close c1 ρ)]
             [C2 (close c2 ρ)])
         (match* ([prove? σ V C1] [prove? σ V C2])
           [('Refuted 'Refuted) (error "WTF??")]
           [(_ 'Refuted) (refine σV C1)]
           [('Refuted _) (refine σV C2)]
           [(_ _) (match V
                    [(val u Cs) (cons σ (val u [intersect-Cs Cs C]))]
                    [(? L? l) (match-let* ([(val u Cs) (σ@ σ l)]
                                           [V′ (val u [intersect-Cs Cs C])])
                                (cons [σ-set σ l V′] l))])]))]
      [(_ [μ-c x c1]) (refine σV [close (subst/c c1 x c) ρ])]
      [([? L? l] [struct-c t cs])
       (match (σ@ σ l)
         [(val (•) Cs) (match-let*
                           ([(cons σ1 ls) (σ++ σ (length cs))]
                            [V′ (val (Struct t ls) Cs)])
                         (refine [cons (σ-set σ1 l V′) l] C))]
         [(val (Struct t Vs) Cs)
          (match-let ([(cons σ′ Us)
                       (let loop ([σi σ] [Us '()] [Vs Vs] [cs cs])
                         (match* (Vs cs)
                           [('() '()) (cons σi (reverse Us))]
                           [([cons Vi Vs′] [cons ci cs′])
                            (match-let ([(cons σ′ Vi′) (refine [cons σi Vi] [close ci ρ])])
                              (loop σ′ [cons Vi′ Us] Vs′ cs′))]))])
            (let ([V′ (val (Struct t Us) Cs)])
              (cons [σ-set σ′ l V′] l)))])]
      [([? L? l] [struct-p t n])
       (match (σ@ σ l)
         [(val (•) Cs) (match-let*
                           ([(cons σ1 ls) (σ++ σ n)]
                            [V′ (val (Struct t ls) ∅)])
                         (for/fold ([σV (cons (σ-set σ1 l V′) l)]) ([C Cs])
                           (refine σV C)))]
         [_ σV])]
      [([val [Struct t Vs] Cs] [struct-c t cs])
       (match-let ([(cons σ′ Us)
                    (let loop ([σi σ] [Us '()] [Vs Vs] [cs cs])
                      (match* (Vs cs)
                        [('() '()) (cons σi (reverse Us))]
                        [([cons Vi Vs′] [cons ci cs′])
                         (match-let ([(cons σ′ Vi′) (refine [cons σi Vi] [close ci ρ])])
                           (loop σ′ [cons Vi′ Us] Vs′ cs′))]))])
         (cons σ′ [val (Struct t Us) Cs]))]
      [([val (•) Cs] [struct-c t cs])
       (match-let ([(cons σ1 Ls) (σ++ σ (length cs))])
         (refine (cons σ1 (val (Struct t Ls) Cs)) C))]
      [([val (•) Cs] [struct-p t n])
       (match-let ([(cons σ1 Ls) (σ++ σ n)])
         (cons σ1 (val (Struct t Ls) ∅)))]
      [([? L? l] _) (match-let ([(cons σ1 V1) (refine [cons σ (σ@ σ l)] C)])
                      (cons [σ-set σ1 l V1] l))]
      
      ; rematerialize for singleton predicates
      [([val u Cs] [op (and p (or 'zero? 'false? 'true?))])
       (cons σ [val (match p ['zero? 0] ['false? #f] ['true? #t]) Cs])]
      [([val u Cs] _)
       (match-let*
           ([Cs1 (intersect-Cs Cs C)]
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
                        (match-let ([(cons σ′ _) (refine (cons σi Li) (close ci ρc))])
                          (loop σ′ Ls′ cs′))]))
                   (Struct t Ls)))])]
            [Cs2 (match Ck
                   [#f Cs1]
                   [(and Ck (close _ _)) (set-remove Cs1 Ck)])])
         (cons σ2 (val u′ Cs2)))])))

(define (intersect-Cs Cs Cn)
  (if (set-empty? Cs) {set Cn}
      (for/fold ([acc ∅]) ([Ci (in-set Cs)])
        (set-union acc (intersect-C Ci Cn)))))

(define (intersect-C Ca Cb)
  (cond
    [(equal? 'Proved (C-prove? Ca Cb)) {set Ca}]
    [(equal? 'Proved (C-prove? Cb Ca)) {set Cb}]
    [else
     (match* (Ca Cb)
       ; unroll recursive ones
       [(_ [close (and c (μ-c x c1)) ρ])
        (intersect-C Ca [close (subst/c c1 x c) ρ])]
       [([close (and c (μ-c x c1)) ρ] _)
        (intersect-C [close (subst/c c1 x c) ρ] Cb)]
       ; break conjunctive ones
       [(_ [close (and-c c1 c2) ρ])
        (set-union (intersect-C Ca [close c1 ρ]) (intersect-C Ca [close c2 ρ]))]
       [([close (and-c c1 c2) ρ] _)
        (set-union (intersect-C [close c1 ρ] Cb) (intersect-C [close c2 ρ] Cb))]
       ; prune stuff in disjunctive ones if possible
       [(_ [close (or-c c1 c2) ρ])
        (let ([Cb′ (truncate Cb Ca)])
          (if (equal? Cb Cb′) {set Ca Cb} (intersect-C Ca Cb′)))]
       [([close (or-c c1 c2) ρ] _)
        (let ([Ca′ (truncate Ca Cb)])
          (if (equal? Ca Ca′) {set Ca Cb} (intersect-C Ca′ Cb)))]
       [(_ _) {set Ca Cb}])]))

; prunes off all branches of disjunction that are excluded by given contract
(define (truncate C1 C2)
  (match-let ([(close c1 ρ1) C1]
              [(close c2 ρ2) C2])
    (match c1
      [(or-c c1l c1r)
       (let ([C1L (close c1l ρ1)]
             [C1R (close c1r ρ1)])
         (match* ([C-prove? C2 C1L] [C-prove? C2 C1R])
           [('Refuted 'Refuted) (error "WTF??")]
           [(_ 'Refuted) (truncate C1L C2)]
           [('Refuted _) (truncate C1R C2)]
           [(_ _) (match-let ([(close c1l′ _) (truncate C1L C2)]
                              [(close c1r′ _) (truncate C1R C2)])
                    (close (or-c c1l′ c1r′) ρ1))]))]
      [_ C1])))

(define (¬ v)
  (f 1 (@ 'Δ [op 'false?] [list (@ 'Δ v [list (x 0)])]) #f))