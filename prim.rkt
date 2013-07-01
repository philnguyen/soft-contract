#lang racket
(require "lang.rkt" "syntax.rkt")
(provide
 (combine-out R? prove? Cs-prove? C-prove? p-prove? simplify-C
              all-prove? all-refute? some-proves? some-refutes?)
 #;(contract-out
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
      ; look up
      [([? L? l] _) (prove? σ [σ@ σ l] C)]
      
      ; break apart/unroll composite contract
      [(_ [and-c c1 c2]) (∧ [prove? σ V (close c1 ρ)] [prove? σ V (close c2 ρ)])]
      [([val _ Cs] [or-c c1 c2])
       (match (Cs-prove? Cs C)
         ['Neither (∨ [prove? σ V (close c1 ρ)] [prove? σ V (close c2 ρ)])]
         [ans ans])]
      [([val _ Cs] [μ-c x c′])
       (match (Cs-prove? Cs C)
         ['Neither (prove? σ V (close (subst/c c′ x c) ρ))]
         [ans ans])]
      
      ; on struct contract
      [([val (Struct t Vs) _] [struct-c t cs])
       (for/fold ([a 'Proved]) ([V Vs] [c cs])
         (match a
           ['Refuted 'Refuted]
           [_ (match (prove? σ V (close c ρ))
                ['Proved a]
                [(and r (or 'Refuted 'Neither)) r])]))]
      [([val (not [? •?]) _] [? struct-c?]) 'Refuted]
      
      ; on procedure contract
      [([val (not [? close?] [? Arr?] [? o?] [? •?]) _] [? func-c?]) 'Refuted]
      
      ; on flat contract
      [(_ [op 'any]) 'Proved]
      [([val 0 _] [op 'zero?]) 'Proved]
      [([val #t _] [op 'true?]) 'Proved]
      [([val #f _] [op 'false?]) 'Proved]
      [([val (? number?) _] [op 'num?]) 'Proved]
      [([val (? boolean?) _] [op 'bool?]) 'Proved]
      [([val (? string?) _] [op 'str?]) 'Proved]
      [([val (? symbol?) _] [op 'symbol?]) 'Proved]
      [([val (? real?) _] [op 'real?]) 'Proved]
      [([val (? integer?) _] [op 'int?]) 'Proved]
      [([val (and [? real?] [? positive?]) _] [op 'positive?]) 'Proved]
      [([val (and [? real?] [? negative?]) _] [op 'negative?]) 'Proved]
      [([val (close [? f?] _) _] [op 'proc?]) 'Proved]
      [([val [? o?] _] [op 'proc?]) 'Proved]
      [([val [? Arr?] _] [op 'proc?]) 'Proved]
      [([val (Arr _ _ _ (close c ρ1) _) _] [? func-c? d])
       (if (and (equal? c d) (equal? ρ ρ1)) 'Proved 'Neither)]
      [([val [Struct t _] _] [struct-p t _]) 'Proved]
      [([val [not (? •?)] _] [? pred?]) 'Refuted]
      
      ; on negation contract
      [(_ (f 1 (@ _ [op 'false?] `(,[@ _ (? pred? o1) `(,[x 0])])) #f))
       (¬ (prove? σ V [close o1 ρ]))]
      
      ; on opaque value
      [([val _ Cs] _) (Cs-prove? Cs C)])))

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
  (for/fold ([a 'Neither]) ([Ci (in-set Cs)])
    (match a
      ['Neither (C-prove? Ci C)]
      [(and r (or 'Proved 'Refuted)) r])))

;; checks whether first contract proves second
(define (C-prove? C D)
  (let go ([C (simplify-C C)] [D (simplify-C D)] [assume ∅])
    (cond
      [(equal? C D) 'Proved]
      [(set-member? assume (cons C D)) 'Proved]
      [else
       (match-let ([(close c ρc) C]
                   [(close d ρd) D])
         (match* (c d)
           [(_ (op 'any)) 'Proved]
           
           ; primitive, type-like contracts
           [([? pred? o1] [? pred? o2]) (p-prove? o1 o2)]
           [([f 1 (@ _ (op 'false?) `(,(@ _ (? pred? o1) `(,(x 0))))) #f] [? pred? o2])
            (match (p-prove? o2 o1)
              ['Proved 'Refuted]
              [_ 'Neither])]
           [([? pred? o1] [f 1 (@ _ (op 'false?) `(,(@ _ (? pred? o1) `(,(x 0))))) #f]) 'Refuted]
           [([f 1 (@ _ (op 'false?) `(,(@ _ (? pred? o1) `(,(x 0))))) #f]
             [f 1 (@ _ (op 'false?) `(,(@ _ (? pred? o2) `(,(x 0))))) #f])
            (p-prove? o2 o1)]
           
           ; struct contract
           [([struct-c t _] [struct-p t _]) 'Proved]
           [([struct-c t cs] [struct-c t ds])
            (for/fold ([a 'Proved]) ([ci cs] [di ds])
              (match a
                ['Refuted 'Refuted]
                [_ (match (go (close ci ρc) (close di ρd) assume)
                     ['Proved a]
                     [ans ans])]))]
           [([? struct-c?] [or (? pred?) (? struct-c?)]) 'Refuted] ; different tag/type
           [([? struct-c?] [? func-c?]) 'Refuted]
           [([struct-p t n] [struct-c t _]) (if (= n 0) 'Proved 'Neither)] ; e.g. cons? ⇒ (cons/c _ _)
           [([? struct-p?] [? struct-c?]) 'Refuted] ; different tag
           [([? struct-p?] [? func-c?]) 'Refuted]
           
           ; func contract
           [([? func-c?] [op 'proc?]) 'Proved]
           [([? func-c?] [? pred? o1]) (p-prove? [op 'proc?] o1)]
           [([func-c cx* cy vc?] [func-c dx* dy vd?])
            (if (and (equal? (length cx*) (length dx*)) (equal? vc? vd?))
                (match (go (close cy ρc) (close dy ρd) assume) ; FIXME: wrong close!!
                  ['Refuted 'Refuted]
                  [_ 'Neither])
                'Refuted)]
           [([op 'proc?] [? func-c?]) 'Neither]
           [([op 'proc?] [? struct-c?]) 'Refuted]
           
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
           [(_ _) 'Neither]))])))

(define/match (simplify-C C)
  [((close (and c (f 1 (@ _ (x sd) (list (x 0))) #f)) ρ))
   (match (ρ@ ρ (- sd 1))
     [(val (? pred? o1) _) (close o1 ρ∅)]
     [(val (close (f 1 (@ _ (? v? v) (list (x 0))) #f) ρv) _)
      (if (set-empty? (FV v)) (simplify-C (close v ρ∅)) C)]
     [(val (Arr _ _ _ _ V) _)
      (simplify-C (close c (ρ-set ρ (- sd 1) V)))]
     [_ C])]
  [((close (f 1 (@ _ (? v? v) (list (x 0))) #f) ρ))
   (if (set-empty? (FV v)) (simplify-C (close v ρ∅)) C)]
  [(_) C])

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