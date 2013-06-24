#lang racket
(require "lang.rkt" "syntax.rkt")
(provide
 R? prove? Cs-prove? C-prove? p-prove?
 #;(contract-out
    [prove? (σ? V? C? . -> . R?)]
    [Cs-prove? ([set/c C?] C? . -> . R?)]
    [C-prove? (C? C? . -> . R?)]
    [p-prove? (pred? pred? . -> . R?)]))

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
       (∨ [Cs-prove? Cs C] [prove? σ V (close c1 ρ)] [prove? σ V (close c2 ρ)])]
      [([val _ Cs] [μ-c x c′]) (∨ (Cs-prove? Cs C) (prove? σ V (close (subst/c c′ x c) ρ)))]
      
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
      [([val [Struct t _] _] [struct-p t _]) 'Proved]
      [([val [not (? •?)] _] [? pred?]) 'Refuted]
      
      ; on negation contract
      [(_ (f 1 (@ _ [op 'false?] `(,[@ _ (? pred? o1) `(,[x 0])])) #f))
       (¬ (prove? σ V [close o1 ρ]))]
      
      ; on opaque value
      [([val _ Cs] _) (Cs-prove? Cs C)])))

;; checks whether given set of contracts can prove new one
(define (Cs-prove? Cs C)
  (for/fold ([a 'Neither]) ([Ci (in-set Cs)])
    (match a
      ['Neither (C-prove? Ci C)]
      [(and r (or 'Proved 'Refuted)) r])))

;; checks whether first contract proves second
(define (C-prove? C1 C2)
  (let go ([C1 C1] [C2 C2] [assumptions ∅])
    (cond
      [(equal? C1 C2) 'Proved]
      [(set-member? assumptions (cons C1 C2)) 'Proved]
      [else
       (match-let ([(close c1 ρ1) C1]
                   [(close c2 ρ2) C2])
         (match* (c1 c2)
           [(_ (op 'any)) 'Proved]
           
           ; primitive, type-like contracts
           [([? pred? o1] [? pred? o2]) (p-prove? o1 o2)]
           [([f 1 (@ _ [op 'false?] `(,[@ _ (? pred? o1) `(,[x 0])])) #f]
             [? pred? o2])
            (match (p-prove? o2 o1)
              ['Proved 'Refuted]
              [_ 'Neither])]
           [([? pred? o1] [f 1 (@ _ [op 'false?] `(,[@ _ (? pred? o1) `(,[x 0])])) #f]) 'Refuted]
           [([f 1 (@ _ [op 'false?] `(,[@ _ (? pred? o1) `(,[x 0])])) #f]
             [f 1 (@ _ [op 'false?] `(,[@ _ (? pred? o2) `(,[x 0])])) #f])
            (p-prove? o2 o1)]
           
           ; struct contract
           [([struct-c t _] [struct-p t _]) 'Proved]
           [([struct-c t cs1] [struct-c t cs2])
            (for/fold ([a 'Proved]) ([d1 cs1] [d2 cs2])
              (match a
                ['Refuted 'Refuted]
                [_ (match (go (close d1 ρ1) (close d2 ρ2) assumptions)
                     ['Proved a]
                     [(and r (or 'Refuted 'Neither)) r])]))]
           [([? struct-c?] [or (? pred?) (? struct-c?)]) 'Refuted] ; different tag/type
           [([? struct-c?] [? func-c?]) 'Refuted]
           [([struct-p t _] [struct-c t _]) 'Neither] ; e.g. cons? ⇒ (cons/c _ _)
           [([? struct-p?] [? struct-c?]) 'Refuted] ; different tag
           [([? struct-p?] [? func-c?]) 'Refuted]
           
           ; func contract
           [([? func-c?] [op 'proc?]) 'Proved]
           [([? func-c?] [? pred? o1]) (p-prove? [op 'proc?] o1)]
           [([func-c cx1 cy1 v1?] [func-c cx2 cy2 v2?])
            (if (and (equal? (length cx1) (length cx2))
                     (equal? v1? v2?))
                (match (go [close cy1 ρ1] [close cy2 ρ2] assumptions) ; FIXME: wrong close!!
                  ['Refuted 'Refuted]
                  [_ 'Neither])
                'Refuted)]
           [([op 'proc?] [? func-c?]) 'Neither]
           [([op 'proc?] [? struct-c?]) 'Refuted]
           
           
           ; break apart/unroll composite contracts
           ; this shouldn't happen often though
           [(_ [and-c c2a c2b]) (∧ (go C1 [close c2a ρ2] assumptions)
                                   (go C1 [close c2b ρ2] assumptions))]
           [(_ [or-c c2a c2b]) (∨ (go C1 [close c2a ρ2] assumptions)
                                  (go C1 [close c2b ρ2] assumptions))]
           [([and-c c1a c1b] _)
            (match* ((go [close c1a ρ1] C2 assumptions)
                     (go [close c1b ρ1] C2 assumptions))
              [('Proved _) 'Proved]
              [(_ 'Proved) 'Proved]
              [('Refuted 'Refuted) 'Refuted]
              [(_ _) 'Neither])]
           [([or-c c1a c1b] _)
            (match* ((go [close c1a ρ1] C2 assumptions)
                     (go [close c1b ρ1] C2 assumptions))
              [('Proved 'Proved) 'Proved]
              [('Refuted 'Refuted) 'Refuted]
              [(_ _) 'Neither])]
           [([μ-c x c1′] _)
            (go (close [subst/c c1′ x c1] ρ1) C2 (set-add assumptions [cons C1 C2]))]
           [(_ [μ-c x c2′]) (go C1 (close [subst/c c2′ x c2] ρ2) assumptions)]
           [(_ _) 'Neither]))])))

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
     [('bool? [or 'true? 'false?]) 'Neither]
     [('num? [or 'real? 'positive? 'negative? 'int? 'zero?]) 'Neither]
     [('real? [or 'positive? 'negative? 'int? 'zero?]) 'Neither]
     [('int? 'zero?) 'Neither]
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