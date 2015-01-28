#lang typed/racket/base
(require racket/match racket/list racket/set racket/string racket/bool
         racket/port racket/system racket/function
         "utils.rkt" "lang.rkt" "runtime.rkt" "show.rkt")
(provide explore →lab call query handled?)

(define-type Z3-Num (U 'Int 'Real))

; query external solver for provability relation
(: query : .σ .V .V → .R)
(define (query σ V C)
  (cond    
   [(not (handled? C)) '?] ; skip when contract is strange
   [else
    #;(printf "Queried with: ~a~n~a~n" (show-Ans σ V) C)
    (define-values (σ′ i) (match V
                            [(.L i) (values σ i)]
                            [(? .//? V) (values (σ-set σ -1 V) -1) #|HACK|#]))
    (define-values (Q* i*) (explore σ′ (set-add (span-C C) i)))
    (define-values (q j*) (gen σ′ i C))
    #;(printf "premises [~a] involve labels [~a] ~n" Q* i*)
    (cond
     ;; Skip querying when the set of labels spanned by premises does not cover
     ;; That spanned by conclusion
     [(not (subset? j* i*)) '?]
     ;; Skip querying when the set of labels spanned by premises only contains
     ;; The single label we ask about (relies on local provability relation
     ;; Being precise enough)
     [(equal? i* {set i}) '?]
     ;; Skip querying when could not generate conclusion
     [(false? q) '?]
     [else
      (call-with
       (string-append*
        (for/list ([i i*])
          (format "(declare-const ~a ~a)~n"
                  (→lab i)
                  (match-let ([(.// _ C*) (σ@ σ′ i)])
                    (or (for/or : (U #f Symbol) ([C : .V C*] #:when (match? C (.// 'integer? _))) 'Int)
                        'Real)))))
       (string-append* (for/list ([q Q*]) (format "(assert ~a)~n" q)))
       q)])]))

(: handled? : .V → Boolean)
(define (handled? C)
  (match? C
    (.// (.λ↓ (.λ 1 (.@ (? arith?) (list (.x 0) (or (.x _) (.b (? number?)))) _)) _) _)
    (.// (.λ↓ (.λ 1 (.@ (or '= 'equal?) (list (.x 0) (or (.x _) (.b (? number?)))) _)) _) _)
    (.// (.λ↓ (.λ 1 (.@ (or '= 'equal?)
                        (list (.x 0)
                              (.@ (? arith?)
                                  (list (or (.x _) (.b (? number?)))
                                        (or (.x _) (.b (? number?)))) _)) _)) _) _)
    (.// (.St 'not/c (list (? handled? C′))) _)))

(: arith? : .expr → Boolean)
(define (arith? e)
  (match? e '= 'equal? '> '< '>= '<=))

; generate all possible assertions spanned by given set of labels
; return set of assertions as wel as set of labels involved
(: explore : .σ (Setof Integer) → (Values (Setof String) (Setof Integer)))
(define (explore σ i*)
  (match-define (.σ m _) σ)
  (define asserts : (Setof String) ∅)
  (define seen : (Setof Integer) ∅)
  (define involved : (Setof Integer) ∅)  
  
  (: visit : Integer → Void)
  (define (visit i)
    (unless (set-member? seen i)
      (match-let ([(and V (.// U C*)) (hash-ref m i)]
                  [queue (ann ∅ (Setof Integer))])
        (when (match? U (.b (? real?)))
          (∪! asserts (format "(= ~a ~a)" (→lab i) (→lab V)))
          (∪! involved i))
        (for ([C C*])
          (let-values ([(q1 j*) (gen σ i C)])
            (∪! queue j*)
            (when (string? q1)
              (∪! asserts q1)
              (∪! involved j*))))
        (∪! seen i)
        (for ([j queue]) (visit j)))))
  (for ([i i*]) (visit i))
  
  (: involved? : (U .V (Listof .V)) → Boolean)
  (define (involved? V)
    (match V
      [(.L i) (set-member? involved i)]
      [(? list? l) (andmap involved? l)]
      [(.// U Cs)
       (match U
         ['• (or (set-member? Cs REAL/C) (set-member? Cs INT/C))]
         [(.b (? real?)) #t]
         [_ #f])]))
  
  ;; Constraint equal inputs -> equal outputs
  (for ([(i Vᵢ) (in-hash m)])
    (match Vᵢ
      [(.// Uᵢ _)
       (when (.Case? Uᵢ)
         (match-define (.Case mappings) Uᵢ)
         (let loop₁ : Void ([pairs : (Listof (Pairof (Listof .V) .L)) (hash->list mappings)])
              (when (cons? pairs)
                (match-define (cons (cons xs₁ y₁) pairs₂) pairs)
                (let loop₂ : Void ([pairs₂ : (Listof (Pairof (Listof .V) .L)) pairs₂])
                     (when (cons? pairs₂)
                       (match-define (cons (cons xs₂ y₂) pairs₃) pairs₂)
                       (∪!
                         asserts
                         (format
                          "~a"
                          `(=>
                            (and ,@(for/list : (Listof Any) ([x₁ xs₁] [x₂ xs₂])
                                     `(= ,(→lab x₁) ,(→lab x₂))))
                            (= ,(→lab y₁) ,(→lab y₂)))))
                       (∪! involved (list->set (for/list : (Listof Integer) ([x xs₁] #:when (.L? x))
                                                 (match-define (.L i) x)
                                                 i)))
                       (∪! involved (list->set (for/list : (Listof Integer) ([x xs₂] #:when (.L? x))
                                                 (match-define (.L i) x)
                                                 i)))
                       (∪! involved (list->set (for/list : (Listof Integer) ([y (list y₁ y₂)]
                                                                         #:when (.L? y))
                                                 (match-define (.L i) y)
                                                 i)))))
                (loop₁ pairs₂))))]
      [_ (void)]))
  
  (values asserts involved))


; generate statement expressing relationship between i and C
; e.g. <L0, (sum/c 1 2)>  translates to  "L0 = 1 + 2"
(: gen : .σ Integer .V → (Values (U #f String) (Setof Integer)))
(define (gen σ i C)
  
  (: type-of : .V → Z3-Num)
  (define (type-of V)
    (match V
      [(.L j) (type-of (σ@ σ j))]
      [(.// (.b (? exact-integer?)) _) 'Int]
      [(.// (.b (? real?)) _) 'Real]
      [(.// '• Cs)
       (cond [(set-member? Cs INT/C) 'Int]
             [else 'Real])]))
  
  (define type-i (type-of (.L i)))
  
  (: maybe-convert : Z3-Num Any → Any)
  (define (maybe-convert t x)
    (cond [(real? x) x]
          [else (match t
                  ['Int (format "(to_real ~a)" x)]
                  [_ x])]))
  
  (match C
    [(? (curry equal? (.¬/C INT/C)))
     ;; Make sure Z3 doesn't consider `1.0` a `(not/c integer?)` by Racket's standard
     (values (format "(not (is_int ~a))" (→lab i))
             (labels i))]
    [(.// (.λ↓ f ρ) _)
     (define ρ@*
       (match-lambda
         [(.b (? number? n)) (Prim n)]
         [(.x i) (ρ@ ρ (- i 1))]))
     (match f
       [(.λ 1 (.@ (? .o? o) (list (.x 0) (and e (or (.x _) (.b (? number?))))) _))
        (define X (ρ@* e))
        (define type-X (type-of X))
        (values
         (cond [(equal? type-i type-X)
                (format "(~a ~a ~a)" (→lab o) (→lab i) (→lab X))]
               [else (format "(~a (to_real ~a) ~a)"
                             (→lab o)
                             (maybe-convert type-i (→lab i))
                             (maybe-convert type-X (→lab X)))])
         (labels i X))]
       [(.λ 1 (.@ (or '= 'equal?)
                  (list (.x 0) (.@ 'sqrt (list (and M (or (.x _) (.b (? real?))))) _)) _))
        (define X (ρ@* M))
        (values (format "(= ~a (^ ~a 0.5))" (→lab i) (→lab X))
                (labels i X))]
       [(.λ 1 (.@ (or '= 'equal?)
                  (list (.x 0) (.@ (? .o? o)
                                   (list (and M (or (.x _) (.b (? number?))))
                                         (and N (or (.x _) (.b (? number?))))) _)) _))
        (define X (ρ@* M))
        (define Y (ρ@* N))
        (define type-X (type-of X))
        (define type-Y (type-of Y))
        (cond
          [(and (equal? type-i type-X) (equal? type-X type-Y))
           (values (format "(= ~a (~a ~a ~a))" (→lab i) (→lab o) (→lab X) (→lab Y))
                   (labels i X Y))]
          [else ; if some operand is Real, convert all to Real
           (values
            (format "(= ~a (~a ~a ~a))"
                    (maybe-convert type-i (→lab i))
                    (→lab o)
                    (maybe-convert type-X (→lab X))
                    (maybe-convert type-Y (→lab Y)))
            (labels i X Y))])]
       [_ (values #f ∅)])]
    [(.// (.St 'not/c (list D)) _)
     (define-values (q i*) (gen σ i D))
     (values (match q [(? string? s) (format "(not ~a)" s)] [_ #f]) i*)]
    [_ (values #f ∅)]))

; perform query/ies with given declarations, assertions, and conclusion,
; trying to decide whether value definitely proves or refutes predicate
(: call-with : String String String → .R)
(define (call-with decs asserts concl)
  (match (call (format "~a~n~a~n(assert (not ~a))~n(check-sat)~n" decs asserts concl))
    [(regexp #rx"^unsat") '✓]
    [(regexp #rx"^sat") 
     (match (call (format "~a~n~a~n(assert ~a)~n(check-sat)~n" decs asserts concl))
             [(regexp #rx"^unsat") 'X]
             [_ #;(printf "?~n") '?])]
    [_ #;(printf "?~n")'?]))

; performs system call to solver with given query
(: call : String → String)
(define (call query)
  #;(printf "Called with:~n~a~n~n" query)
  (with-output-to-string
   (λ () ; FIXME: lo-tech. I don't know Z3's exit code
     (system (format "echo \"~a\" | z3 -in -smt2" query)))))

; generate printable/readable element for given value/label index
(: →lab : (U Integer .V .o) → (U Real String Symbol))
(define →lab
  (match-lambda
    [(.// (.b (? real? x)) _) x]
    [(or (.L i) (? integer? i))
     (if (integer? i)
         (if (>= i 0) (format "L~a" i) (format "X~a" (- i)))
         (error "can't happen"))]
    [(? symbol? o) o]))

; extracts all labels in contract
(: span-C : .V → (Setof Integer))
(define span-C
  (match-lambda
    [(.// (.λ↓ _ (.ρ m _)) _)
     (for/set: : (Setof Integer) ([V (in-hash-values m)] #:when (.L? V))
       (match-let ([(.L i) V]) i))]
    [_ ∅]))

;; syntactic sugar
(define-syntax-rule (∪! s i)
  (set! s (let ([x i]) (if (set? x) (set-union s x) (set-add s i)))))
(: labels : (U .V Integer) * → (Setof Integer))
(define (labels . V*)
  (for/set: : (Setof Integer) ([V V*] #:when (match? V (? integer?) (.L _)))
    (match V
      [(? integer? i) i]
      [(.L i) i])))
