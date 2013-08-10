#lang racket
(require "lang.rkt" "syntax.rkt" "query-helper.rkt")
(provide
 #;(combine-out R? prove? Cs-prove? C-prove? p-prove? simplify-C
              all-prove? all-refute? some-proves? some-refutes?)
 (contract-out
  [prove? (σ? V? C? . -> . R?)]
  [Cs-prove? ([set/c C?] C? . -> . R?)]
  [C-prove? (C? C? . -> . R?)]
  [p-prove? (pred? pred? . -> . R?)]
  [simplify-C (C? . -> . C?)]
  [all-prove? (σ? (listof V?) C? . -> . any/c)]
  [all-refute? (σ? (listof V?) C? . -> . any/c)]
  [some-proves? (σ? (listof V?) C? . -> . any/c)]
  [some-refutes? (σ? (listof V?) C? . -> . any/c)]))

(define R? (or/c 'Proved 'Refuted 'Neither))

;; checks whether value satisfies contract
(define (prove? σ V C)
  (match-let ([(close c ρ) C])
    (match* (V c)
      [(_ (op 'any)) 'Proved]
      
      ; defer predicates on real numbers to CVC4
      #;[(V (f 1 (@ _ (op (or 'equal? '= '< '> '>= '<=)) (list (x 0) _)) #f)) (query σ V C)]
      
      ; look up. Important not to lookup before querying CVC4
      [([? L? l] _) (prove? σ [σ@ σ l] C)]
      [((val (•) Cs) _) (Cs-prove? Cs C)]
      [((val U Cs) _) (match (U-prove? σ U C)
                        ['Neither (Cs-prove? Cs C)]
                        [r r])])))

(define (U-prove? σ U C) ; U ≠ •
  (match-let ([(close c ρ) (simplify-C C)])
    (match* (U c)
      ; base
      [(#t (op 'true?)) 'Proved]
      [(#f (op 'false?)) 'Proved]
      [((? number?) (op 'num?)) 'Proved]
      [((? real?) (op 'real?)) 'Proved]
      [((? integer?) (op 'int?)) 'Proved]
      [((? string?) (op 'str?)) 'Proved]
      [((? boolean?) (op 'bool?)) 'Proved]
      [((? symbol?) (op 'symbol?)) 'Proved]
      
      ; special rules for reals
      [((? b? b1)
        (f 1 (@ _ (op (or 'equal? '=)) (or (list (x 0) (? b? b2)) (list (? b? b2) (x 0)))) #f))
       (if (equal? b1 b2) 'Proved 'Refuted)]
      [((? real? r1)
        (f 1 (or (@ _ (op '>=) (or (list (x 0) (? real? r2))))
                 (@ _ (op '<=) (or (list (? real? r2) (x 0))))) #f))
       (if (>= r1 r2) 'Proved 'Refuted)]
      [((? real? r1)
        (f 1 (or (@ _ (op '>) (or (list (x 0) (? real? r2))))
                 (@ _ (op '<) (or (list (? real? r2) (x 0))))) #f))
       (if (> r1 r2) 'Proved 'Refuted)]
      [((? real? r1)
        (f 1 (or (@ _ (op '<=) (or (list (x 0) (? real? r2))))
                 (@ _ (op '>=) (or (list (? real? r2) (x 0))))) #f))
       (if (<= r1 r2) 'Proved 'Refuted)]
      [((? real? r1)
        (f 1 (or (@ _ (op '<) (or (list (x 0) (? real? r2))))
                 (@ _ (op '>) (or (list (? real? r2) (x 0))))) #f))
       (if (< r1 r2) 'Proved 'Refuted)]
      
      ; procedures
      [((or (close (? f?) _) (? Arr?) (? o?)) (op 'proc?)) 'Proved]
      [((Arr _ _ _ (close d ρ1) _) (? func-c?))
       (if (and (equal? c d) (equal? ρ1 ρ)) 'Proved 'Neither)]
      ; structs
      [((Struct t _) (struct-p t _)) 'Proved]
      [((Struct t Vs) (struct-c t cs))
       (for/fold ([a 'Proved]) ([Vi Vs] [ci cs])
         (match a
           ['Refuted 'Refuted]
           [_ (match (prove? σ Vi (close ci ρ))
                ['Proved a]
                [r r])]))]
      ; definite refutes
      [((not (? close?) (? Arr?) (? o?)) (? func-c?)) 'Refuted]
      [(_ (? struct-c?)) 'Refuted]
      [(_ (? pred?)) 'Refuted]
      
      ; break/unroll composite contracts
      [(_ (and-c c1 c2)) (∧ (U-prove? σ U (close c1 ρ)) (U-prove? σ U (close c2 ρ)))]
      [(_ (or-c c1 c2)) (∨ (U-prove? σ U (close c1 ρ)) (U-prove? σ U (close c2 ρ)))]
      [(_ (μ-c x d)) (U-prove? σ U (close (subst/c d x c) ρ))]
      
      ; negation
      [(_ (f 1 (@ _ (op 'false?) (list e)) #f)) (¬ (U-prove? σ U (close (f 1 e #f) ρ)))]
      
      ; conservative default
      [(_ _) 'Neither])))

;; checks whether all/some value(s) satisfy/refute contract
(define (all-prove? σ Vs C)
  (for/and ([V Vs]) (equal? 'Proved (prove? σ V C))))
(define (all-refute? σ Vs C)
  (for/and ([V Vs]) (equal? 'Refuted (prove? σ V C))))
(define (some-proves? σ Vs C)
  (for/or ([V Vs]) (equal? 'Proved (prove? σ V C))))
(define (some-refutes? σ Vs C)
  (for/or ([V Vs]) (equal? 'Refuted (prove? σ V C))))

;; checks whether given set of contracts can prove new one
(define (Cs-prove? Cs C)
  (or (for*/first ([Ci (in-set Cs)]
                   [r (in-value (C-prove? Ci C))]
                   #:when (match? r 'Proved 'Refuted))
        r)
      'Neither))

;; checks whether first contract proves second
(define (C-prove? C D)
  (let go ([C C] [D D] [assume ∅])
    (let ([C (simplify-C C)] [D (simplify-C D)])
      (cond
        [(equal? C D) 'Proved]
        [(set-member? assume (cons C D)) 'Proved]
        [else
         (match-let ([(close c ρc) C] [(close d ρd) D])
           (match* (c d)
             [(_ (op 'any)) 'Proved]
             
             ; primitive, type-like contracts
             [([? pred? o1] [? pred? o2]) (p-prove? o1 o2)]
             
             ; eliminate negation
             [((f 1 (@ _ (op 'false?) (list ec)) #f) (f 1 (@ _ (op 'false?) (list ed)) #f))
              (go (close (f 1 ed #f) ρd) (close (f 1 ec #f) ρc) assume)]
             [((f 1 (@ _ (op 'false?) (list ec)) #f) _)
              (match (go D (close (f 1 ec #f) ρc) assume)
                ['Proved 'Refuted]
                [_ 'Neither])]
             [(_ (f 1 (@ _ (op 'false?) (list ed)) #f))
              (¬ (go C (close (f 1 ed #f) ρd) assume))]
             
             ; special rules for reals
             [((f 1 (@ _ (op '>) (list (x 0) (? real? r1))) #f)
               (f 1 (@ _ (op (or '> '>=)) (list (x 0) (? real? r2))) #f))
              (if (>= r1 r2) 'Proved 'Neither)]
             [((f 1 (@ _ (op '>) (list (x 0) (? real? r1))) #f)
               (f 1 (@ _ (op (or '= '< '<=)) (list (x 0) (? real? r2))) #f))
              (if (>= r1 r2) 'Refuted 'Neither)]
             
             [((f 1 (@ _ (op '>=) (list (x 0) (? real? r1))) #f)
               (f 1 (@ _ (op '>) (list (x 0) (? real? r2))) #f))
              (if (> r1 r2) 'Proved 'Neither)]
             [((f 1 (@ _ (op '>=) (list (x 0) (? real? r1))) #f)
               (f 1 (@ _ (op '>=) (list (x 0) (? real? r2))) #f))
              (if (>= r1 r2) 'Proved 'Neither)]
             [((f 1 (@ _ (op '>=) (list (x 0) (? real? r1))) #f)
               (f 1 (@ _ (op (or '<= '=)) (list (x 0) (? real? r2))) #f))
              (if (> r1 r2) 'Refuted 'Neither)]
             [((f 1 (@ _ (op '>=) (list (x 0) (? real? r1))) #f)
               (f 1 (@ _ (op '<) (list (x 0) (? real? r2))) #f))
              (if (>= r1 r2) 'Refuted 'Neither)]
             
             [((f 1 (@ _ (op '=) (list (x 0) (? real? r1))) #f)
               (f 1 (@ _ (op n) (list (x 0) (? real? r2))) #f))
              (if ((match n ['= =] ['> >] ['>= >=] ['<= <=] ['< <]) r1 r2) 'Proved 'Refuted)]
             
             [((f 1 (@ _ (op '<=) (list (x 0) (? real? r1))) #f)
               (f 1 (@ _ (op '<) (list (x 0) (? real? r2))) #f))
              (if (< r1 r2) 'Proved 'Neither)]
             [((f 1 (@ _ (op '<=) (list (x 0) (? real? r1))) #f)
               (f 1 (@ _ (op '<=) (list (x 0) (? real? r2))) #f))
              (if (<= r1 r2) 'Proved 'Neither)]
             [((f 1 (@ _ (op '<=) (list (x 0) (? real? r1))) #f)
               (f 1 (@ _ (op (or '>= '=)) (list (x 0) (? real? r2))) #f))
              (if (< r1 r2) 'Refuted 'Neither)]
             [((f 1 (@ _ (op '<=) (list (x 0) (? real? r1))) #f)
               (f 1 (@ _ (op '>) (list (x 0) (? real? r2))) #f))
              (if (<= r1 r2) 'Refuted 'Neither)]
             
             [((f 1 (@ _ (op '<) (list (x 0) (? real? r1))) #f)
               (f 1 (@ _ (op (or '< '<=)) (list (x 0) (? real? r2))) #f))
              (if (<= r1 r2) 'Proved 'Neither)]
             [((f 1 (@ _ (op '<) (list (x 0) (? real? r1))) #f)
               (f 1 (@ _ (op (or '= '> '>=)) (list (x 0) (? real? r2))) #f))
              (if (<= r1 r2) 'Refuted 'Neither)]
             
             ; struct contract
             [([struct-c t _] [struct-p t _]) 'Proved]
             [([struct-p t n] [struct-c t _]) (if (= n 0) 'Proved 'Neither)] ; e.g. empty? ⇒ (empty)
             [([struct-c t cs] [struct-c t ds])
              (for/fold ([a 'Proved]) ([ci cs] [di ds])
                (match a
                  ['Refuted 'Refuted]
                  [_ (match (go (close ci ρc) (close di ρd) assume)
                       ['Proved a]
                       [r r])]))]
             [((or (? struct-c?) (? struct-p?)) (or (? pred?) (? struct-c?) (? func-c?))) 'Refuted] ; different tag/type
             
             ; func contract
             [([? func-c?] [op 'proc?]) 'Proved]
             [([? func-c?] [? pred? o1]) (p-prove? [op 'proc?] o1)]
             [([func-c cx* cy vc?] [func-c dx* dy vd?]) ; FIXME limited for now
              (cond
                [(not (= (length cx*) (length dx*))) 'Refuted]
                [(equal? 'Refuted (go (close cy ρc) (close dy ρd) assume)) 'Refuted]
                [(for/first ([ci cx*] [di dx*] #:when (match? (go (close ci ρc) (close di ρd) assume) 'Refuted)) #t) 'Refuted]
                [else 'Neither])]
             [((op 'proc?) (? func-c?)) 'Neither]
             [((op 'proc?) (or (? struct-c?) (? struct-p?) (? pred?))) 'Refuted]
             
             [([μ-c x c1] [μ-c z d1]) (go (close (subst/c c1 x c) ρc)
                                          (close (subst/c d1 z d) ρd)
                                          (set-add assume (cons C D)))]
             [([μ-c x c1] _) (go (close (subst/c c1 x c) ρc) D (set-add assume (cons C D)))]
             [(_ [μ-c x d1]) (go C (close (subst/c d1 x d) ρd) (set-add assume (cons C D)))]
             
             ; break apart/unroll composite contracts
             ; this shouldn't happen often though
             [([or-c c1 c2] _)
              (match* ((go (close c1 ρc) D assume) (go (close c2 ρc) D assume))
                [('Proved 'Proved) 'Proved]
                [('Refuted 'Refuted) 'Refuted]
                [(_ _) 'Neither])]
             [(_ [and-c d1 d2]) (∧ (go C (close d1 ρd) assume) (go C (close d2 ρd) assume))]
             [(_ [or-c d1 d2]) (∨ (go C (close d1 ρd) assume) (go C (close d2 ρd) assume))]
             [([and-c c1 c2] _)
              (match* ((go (close c1 ρc) D assume) (go (close c2 ρc) D assume))
                [('Proved _) 'Proved]
                [(_ 'Proved) 'Proved]
                [('Refuted 'Refuted) 'Refuted]
                [(_ _) 'Neither])]
             [(_ _) 'Neither]))]))))

(define (simplify-C C)
  (match-let ([(close c ρ) C])
    (match c
      ; η-simplify
      [(f 1 (@ _ (x sd) (list (x 0))) #f)
       (match (ρ@ ρ (- sd 1))
         [(val (? pred? o1) _) (close o1 ρ∅)]
         [(val (close (f 1 (@ _ (? v? v) (list (x 0))) #f) ρv) _)
          (if (closed? v) (simplify-C (close v ρ∅)) C)]
         [(val (Arr _ _ _ _ V) _)
          (simplify-C (close c (ρ-set ρ (- sd 1) V)))]
         [_ C])]
      [(f 1 (@ _ (? v? v) (list (x 0))) #f)
       (if (set-empty? (FV v)) (simplify-C (close v ρ∅)) C)]
      
      ; inline base values in simple contracts
      [(f 1 (@ l e (list x1 x2)) #f)
       (let* ([ρ@* (match-lambda
                     [(and z (x (? positive? sd)))
                      (match (ρ@ ρ (- sd 1))
                        [(val (? b? b) _) b]
                        [_ z])]
                     [e e])]
              [z1 (ρ@* x1)]
              [z2 (ρ@* x2)])
         (if (and (eq? z1 x1) (eq? z2 x2)) C
             (close-c (f 1 (@ l e (list z1 z2))) ρ)))]
      [_ C])))

;; checks whether first predicate implies second
(define/match (p-prove? P1 P2)
  [(_ [op 'any]) 'Proved]
  [(o o) 'Proved]
  [([op 'any] _) 'Neither]
  [([op p1] [op p2])
   (match* (p1 p2)
     [([or 'true? 'false?] 'bool?) 'Proved]
     [([or 'real? 'positive? 'negative? 'int? 'zero?] 'num?) 'Proved]
     [([or 'positive? 'negative? 'int? 'zero?] 'real?) 'Proved]
     [('zero? 'int?) 'Proved]
     [([or 'positive? 'negative?] 'int?) 'Neither]
     [('bool? [or 'true? 'false?]) 'Neither]
     [('num? [or 'real? 'positive? 'negative? 'int? 'zero?]) 'Neither]
     [('real? [or 'positive? 'negative? 'int? 'zero?]) 'Neither]
     [('int? [or 'positive? 'negative? 'zero?]) 'Neither]
     [(_ _) 'Refuted])]
  [(_ _) 'Refuted])

(define-syntax ∨
  (syntax-rules ()
    [(_ e) e]
    [(_ e1 e ...) (match e1
                    ['Proved 'Proved]
                    ['Refuted (∨ e ...)]
                    ['Neither (match (∨ e ...)
                                ['Proved 'Proved]
                                [_ 'Neither])])]))

(define-syntax ∧
  (syntax-rules ()
    [(_ e) e]
    [(_ e1 e ...) (match e1
                    ['Proved (∧ e ...)]
                    ['Refuted 'Refuted]
                    ['Neither (match (∧ e ...)
                                ['Refuted 'Refuted]
                                [_ 'Neither])])]))

(define/match (¬ _)
  [('Proved) 'Refuted]
  [('Refuted) 'Proved]
  [('Neither) 'Neither])