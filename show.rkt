#lang racket
(require
 "lang.rkt"
 (only-in redex variables-not-in))

(define vars-not-in
  (let* ([pool '(x y z u v w a b c)]
         [N (length pool)])
    (λ (n t)
      (reverse ; just for nice order
       (variables-not-in t (if (<= n N) (take pool n) (make-list n 'x1)))))))

(provide
 #;(all-defined-out)
 (contract-out
  [show-A (σ? A? . -> . any)]
  [show-σA (σ? A? . -> . (cons/c any/c any/c))]
  [show-E (E? . -> . any)]
  [show-U (U? . -> . any)]
  [show-C (C? . -> . any)]
  [show-c (c? . -> . any)]
  [show-e (e? . -> . any)]
  [show-b (b? . -> . any)]
  [show-ρ (ρ? . -> . any)]))

;; readable evaluation answer
(define (show-A σ a)
  (match a
    [(? L? l) (show-A σ [σ@ σ l])]
    [(Blm f+ fo s) (show-E a)]
    [(val w Cs)
     (match w
       [(? b? b) (show-b b)]
       [(or [? Arr?] [? o?] [close [? f?] _]) 'function]
       [(Struct t Vs) `(,t ,@ (map (curry show-A σ) Vs))]
       [(•) (match (for/list ([C (in-set Cs)]) (show-C C))
              ['() '•]
              [Cs (cons '• Cs)])])]))

;; full final state with heap
(define (show-σA σ1 a)
  (cons (show-E a) (match-let ([(σ m l) σ1])
                     (for/list ([L (range 0 l)])
                       (list (show-E L) '↦ (show-E (hash-ref m L)))))))

(define/match (show-E E)
  [((close e _)) (show-e e)]
  [((val U Cs)) (match U
                  [(•) (cons '• (for/list ([C Cs]) (show-C C)))]
                  [_ (show-U U)])]
  [((Blm l+ lo s)) `(blame ,l+ ,lo ,s)]
  [((? L? l)) (string->symbol (string-append "L" (num-subscript l)))]
  [((Mon _ _ _ C E)) `(MON ,(show-C C) ,(show-E E))]
  [((FC _ C V)) `(FC ,(show-C C) ,(show-E V))]
  [((Assume V C)) `(ASSUME ,(show-E V) ,(show-C C))])

(define/match (show-U U)
  [((close f _)) (show-e f)]
  [((•)) `•]
  [((Struct t Vs)) (match (length Vs)
                     [0 t]
                     [_ `(,t ,@ (map show-E Vs))])]
  [((Arr _ _ _ C V)) `(=> ,(show-C C) ,(show-E V))]
  [((? b? b)) (show-b b)])

(define/match (show-C C)
  [((close c _)) (show-c c)])

(define/match (show-c c)
  [((func-c xs y v?)) `(,@ (map show-c xs) ,(if v? '↦* '↦) ,(show-c y))]
  [((and-c c1 c2)) `(and/c ,(show-c c1) ,(show-c c2))]
  [((or-c c1 c2)) `(or/c ,(show-c c1) ,(show-c c2))]
  [((struct-c t cs))
   `(,(string->symbol (string-append (symbol->string t) "/c")) ,@ (map show-c cs))]
  [((μ-c x c)) `(μ ,x ,(show-c c))]
  [((? v? v)) (show-e v)])

(define (show-e e [ctx '()])
  (match e
    [(f 1 (@ _ (op 'false?) (list (@ _ (? v? v) (list (x 0))))) #f) `(¬ ,(show-e v))]
    [(f 1 (@ _ e1 (list (x 0))) #f) (show-e e1)]
    [(f n e _) (let ([xs (vars-not-in n ctx)])
                 `(λ ,xs ,(show-e e (append xs ctx))))]
    [(•) '•]
    [(x sd) (if (< sd (length ctx)) (list-ref ctx sd)
                (string->symbol (string-append "⋯" (num-subscript sd))))]
    [(ref _ _ x) x]
    [(@ _ (f 1 (if/ (x 0) (x 0) e2) #f) (list e1))
     `(,(show-e e1 ctx) ∨ ,(show-e e2 ctx))]
    [(@ _ (f n ey #f) (list ex ...))
     (let ([xs (vars-not-in n ctx)])
       `(let ,(for/list ([x (reverse xs)] [e ex]) `[,x ,(show-e e ctx)])
          ,(show-e ey (append xs ctx))))]
    [(@ _ f xs) `(,(show-e f ctx) ,@ (for/list ([x xs]) (show-e x ctx)))]
    [(if/ e1 e2 #t) `(,(show-e e1 ctx) ⇒ ,(show-e e2 ctx))]
    [(if/ e1 e2 #f) `(,(show-e e1 ctx) ∧ ,(show-e e2 ctx))]
    [(if/ e1 e2 e3) `(if ,(show-e e1 ctx) ,(show-e e2 ctx) ,(show-e e3 ctx))]
    [(amb _) 'amb]
    [(? b? b) (show-b b)]))

(define/match (show-b b)
  [((op name)) (match name ['false? '¬] ['<= '≤] ['>= '≥] [_ name])]
  [((struct-mk t _)) t]
  [((struct-p t _)) (string->symbol (string-append (symbol->string t) "?"))]
  [((struct-ac t n i)) (string->symbol (string-append (symbol->string t) "-" (number->string i)))]
  [((? string? s)) (string-append "\"" s "\"")]
  [(b) b])

(define (show-ρ ρ1)
  (match-let ([(ρ m l) ρ1])
    (for/list ([(i V) (in-hash m)])
      (let ([sd (- l i 1)])
        (list sd '↦ (show-E V))))))

(define (num-subscript n)
  ((and/c integer? (not/c negative?)) . -> . string?)
  (match n
    [0 "₀"] [1 "₁"] [2 "₂"] [3 "₃"] [4 "₄"]
    [5 "₅"] [6 "₆"] [7 "₇"] [8 "₈"] [9 "₉"]
    [_ (string-append (num-subscript (quotient n 10))
                      (num-subscript (remainder n 10)))]))