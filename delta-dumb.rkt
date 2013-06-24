#lang racket
(require
 "lang.rkt" "prim.rkt" "syntax.rkt"
 (only-in "delta.rkt" (Δ Δ0) (refine refine0)))
(provide #;(combine-out Δ refine)
         (contract-out
          [Δ (l? σ? o? [listof V?] . -> . (nd/c (cons/c σ? A?)))]
          [refine ((cons/c σ? V?) C? . -> . (nd/c (cons/c σ? V?)))]))

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
          [(cons σ2 (val #t _)) (cons σ2 [δ name (map [curry σ@* σ2] Vs)])]
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
   (val ((match name ['< <] ['> >] [>= >=] [<= <=]) x y) ∅)]
  [('str-len `(,[val (? string? x) _])) (val (string-length x) ∅)]
  
  ; semi-precise values
  [('* (or `(,[val 0 _] ,_) `(,_ ,[val 0 _]))) (val 0 ∅)]
  [('/ `(,[val 0 _] ,_)) (val 0 ∅)]
  [('/ `(,[val (? real?) _] ,_))
   (val (•) {set (close [op 'real?] ρ∅) (close [¬ (op 'zero?)] ρ∅)})]
  [('/ `(,[val (? number?) _] ,_))
   (val (•) {set (close [op 'num?] ρ∅) (close [¬ (op 'zero?)] ρ∅)})]
  [('/ Vs)
   (match (map (λ (vi) (prove? σ∅ vi [close (op 'real?) ρ∅])) Vs)
     [`(Proved ...) (val [•] {set (close [op 'real?] ρ∅)})]
     [_ (val [•] {set (close [op 'num?] ρ∅)})])]
  [([or '+ '- '* 'add1 'sub1] Vs)
   (match (map (λ (vi) (prove? σ∅ vi [close (op 'int?) ρ∅])) Vs)
     [`(Proved ...) (val [•] {set (close [op 'int?] ρ∅)})]
     [_ (match (map (λ (vi) (prove? σ∅ vi [close (op 'real?) ρ∅])) Vs)
          [`(Proved ...) (val [•] {set (close [op 'real?] ρ∅)})]
          [_ (val [•] {set (close [op 'num?] ρ∅)})])])]
  
  ; abstract result...
  [('str-len _) (val (•) {set (close [op 'int?] ρ∅)})]
  [([or '> '< '>= '<=] _) (val (•) {set (close [op 'bool?] ρ∅)})])

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
(define (check-p σ0 V0 p)
  (match (prove? σ0 V0 [close p ρ∅])
    ['Proved (cons σ0 TT)]
    ['Refuted (cons σ0 FF)]
    ['Neither {set (cons σ0 TT) (cons σ0 FF)}]))

(define (refine σV C)
  (match-let ([(close c ρ) C]
              [(cons σ V) σV])
    (match c
      [(or-c c1 c2) (let ([C1 (close c1 ρ)]
                          [C2 (close c2 ρ)])
                      (match* ((prove? σ V C1) (prove? σ V C2))
                        [(_ 'Refuted) (refine σV C1)]
                        [('Refuted _) (refine σV C2)]
                        [(_ _) (∪ (refine σV C1) (refine σV C2))]))]
      [(μ-c x c1) (refine σV (close (subst/c c1 x c) ρ))]
      [_ (refine0 σV C)])))

(define (¬ v)
  (f 1 (@ 'Δ [op 'false?] [list (@ 'Δ v [list (x 0)])]) #f))