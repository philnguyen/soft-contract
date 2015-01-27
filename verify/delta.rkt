#lang typed/racket/base
(require racket/match racket/set racket/list racket/function racket/bool
         "../utils.rkt" "../lang.rkt" "../runtime.rkt" "../provability.rkt" "../show.rkt"
         (prefix-in raw: "../delta.rkt"))
(provide δ ⊕ refine alloc)

(: δ : .σ .o (Listof .V) Mon-Party → .Ans*)
(define (δ σ o Vs l)
  (parameterize ([raw:refine1 refine1])
    (raw:δ σ o Vs l)))

(: refine : .σ .V (U (Setof .V) (Listof .V) .V) * → .Vns)
(define (refine σ V . Css)
  (parameterize ([raw:refine1 refine1])
    (apply raw:refine σ V Css)))

(: alloc : (case-> [.σ .V → .Vns]
                   [.σ (Listof .V) → (Pairof .σ (Listof .V))]))
(define (alloc σ V)
  (parameterize ([raw:refine1 refine1])
    (raw:alloc σ V)))

(: refine1 : .σ .V .V → .Vns)
(define (refine1 σ V C)
  (let ([C (simplify C)])
    #;(printf "refine1:~n~a~n~a~n~a~n~n" (show-σ σ) (show-E σ V) (show-E σ C))
    (when (match? C (.// '• _)) (error "ha!"))
    (match V
      [(.L i) (match-let ([(cons σ′ V′) (refine1 σ (σ@ σ i) C)])
                (match V′
                  [(.// (.St t V*) C*) (match-let* ([(cons σ′ V*′) (raw:alloc σ′ V*)]
                                                    [V′ (.// (.St t V*′) C*)])
                                         (cons (σ-set σ′ i V′) V))]
                  [(? .//? V′) (cons (σ-set σ′ i V′) V)]
                  [(? .μ/V? V′) (cons (σ-set σ′ i V′) V)] ; duplicate to get around TR
                  [_ (error "broken =_=" V)]))
       #;(match (refine1 σ (σ@ σ i) C)
       [(cons σ (? .L? L)) (cons σ L)]
       [(cons σ′ V′) (if (or (.//? V′) (.μ/V? V′))
                         (cons (σ-set σ′ i V′) V)
                         (error "broken: " V′))])]
    [(.// U C*)
     (match C
       [(.L _) (cons σ (.// U (set-add C* C)))]
       [(.// Uc _)          
        (match Uc
          [(.St 'and/c (list C1 C2)) (raw:refine σ V C1 C2)]
          [(.St 'or/c (list C1 C2))
           (match* ((⊢ σ V C1) (⊢ σ V C2))
             [('X 'X) (error "WTF??")]
             [(_ 'X) (refine1 σ V C1)]
             [('X _) (refine1 σ V C2)]
             [(_ _) (cons σ (.// U (raw:refine-C* C* C)))])]
          [(and Uc (.μ/C x C′))
           (match U
             ['• (cons σ (reify C))]
             [(.St t V*) (refine1 σ V (unroll/C Uc))]
             [_ (cons σ V)])]
          ; equal contracts
          [(.λ↓ (.λ 1 (.@ (or '= 'equal?) (list (.x 0) e) _)) ρ)
           (match e
             [(? .b? b) (cons σ (.// b C*))]
             [(and (? .λ? f) (? closed?)) (cons σ (.// (.λ↓ f ρ∅) C*))]
             [(.x i) (match (ρ@ ρ (- i 1))
                       [(.L a) (match-let ([(.// U′ C*′) (σ@ σ a)])
                                 (cons σ (.// (raw:U+ U U′) (raw:∪ C* C*′ C))))]
                       [(.// U′ C*′) (cons σ (.// (raw:U+ U U′) (raw:∪ C* C*′)))])]
             [_ (cons σ (.// U (set-add C* C)))])]
          ; struct contracts
          [(.St/C t D*)
           (match-let* ([(cons σ V*) (ann (match U
                                            ['•
                                             (let-values ([(σ Vs) (σ++ σ (length D*))])
                                               (cons σ Vs))]
                                            [(.St _ V*) (cons σ V*)])
                                          (Pairof .σ (Listof .V)))]
                        [(cons σ V*) (raw:refine* σ V* D*)])
             (cons σ (.// (.St t V*) C*)))]
          [(.st-p t n) (match U
                         ['•
                          (let-values ([(σ′ L*) (σ++ σ n)])
                            (cons σ′ (.// (.St t L*) C*)))]
                         [(.St (? (curry eq? t)) _) (cons σ V)])]
          ; singleton contracts
          ['true? (cons σ (.// .tt C*))]
          ['false? (cons σ (.// .ff C*))]
          [(.st-p t 0) (cons σ (.// (.St t '()) C*))]
          [_ (cons σ (.// U (set-add C* C)))])])]
    [(and (.μ/V x V*) V)
     (let*-values ([(σ′ V*′)
                    (for/fold ([σ : .σ σ] [Vs : (Setof .V) ∅]) ([Vi V*])
                      (match (⊢ σ Vi C)
                        ['✓ (values σ (set-add Vs Vi))]
                        ['X (values σ Vs)]
                        ['? (match-let* ([(cons σ′ Vj) (refine1 σ Vi C)]
                                               [(cons Vj′ Vs′) (elim-μ x Vj)])
                                    (values σ′ (compact (compact Vs Vs′) {set Vj′})))]))])
       #;(printf "new V* is ~a~n~n" (for/set: Any ([Vi V*′]) (show-V σ′ Vi)))
       (match (set-count V*′)
         [0 (error "bogus refinement") #;V∅]
            [1 (cons σ′ (V/ (set-first V*′) (.X/V x) V))]
            [_ (cons σ′ (μV x V*′))]))]
     [(? .X/V? x) (cons σ x)]))) ; abuse μ for non-inductive set

(: v-class : .σ (U .V (Setof .V)) → (Setof Any))
(define (v-class σ x)
  (match x
    [(.L i) (v-class σ (σ@ σ i))]
    [(.// U C*)
     (match U
       ['• (or (for/or : (Option (Setof Any)) ([C : .V C*] #:when (match? C (.// (? .pred?) _)))
                 (match-define (.// (? .pred? o) _) C)
                 {set (name o)})
               {set '•})]
       [(? .o? o) {set `(prim ,(name o))}]
       [(.b u) {set (cond
                      [(integer? u) 'integer?]
                      [(real? u) 'real?]
                      [(number? u) 'number?]
                      [(string? u) 'string?]
                      [(false? #f) 'false?]
                      [(eq? u #t) 'true?]
                      [(symbol? u) 'symbol?]
                      [else 'misc])}]
       [(.Ar _ V _) (v-class σ V)]
       [(.St t _) {set t}]
       [(.λ↓ (.λ n _) _) {set `(proc? ,n)}]
       [_ {set 'misc}])]
    [(.μ/V _ V*) (v-class σ V*)]
    [(.X/V _) ∅]
    [(? set? s) (for/fold ([acc : (Setof Any) ∅]) ([i s])
                  (set-union acc (v-class σ i)))]))

;; biased approximation
(: ⊕ : (case→ 
        [.σ .V .σ .V → (Pairof .σ .V)]
        [.σ (Listof .V) .σ (Listof .V) → (Pairof .σ (Listof .V))]
        [.σ .σ .F → .σ]
        [.V .V → .V]
        [(Listof .V) (Listof .V) → (Listof .V)]
        [.ρ .ρ → .ρ]))
(define ⊕
  #;(printf "⊕:~n~n~a~n~nand~n~n~a~n~n~n" V0 V1)
  (case-lambda
    [(σ0 V0 σ1 V1)
     (match* (V0 V1)
       [((? .V? V0) (? .V? V1))
        (match-let ([Vi (⊕ (V-abs σ0 V0) (V-abs σ1 V1))])
          (match V1
            [(.L i) (match-let ([(cons σ1′ Vi′) (raw:alloc σ1 Vi)])
                      (match Vi′
                        [(.L j) (cons (σ-set σ1′ i (σ@ σ1′ j)) V1)]
                        [(and Vi′ (or (? .//?) (? .μ/V?))) (cons (σ-set σ1′ i Vi′) V1)]
                        [_ (error "⊕: impossible: .X/V")]))]
            [_ (raw:alloc σ1 Vi)]))
        #;(let ([Vi (⊕ (V-abs σ0 V0) (V-abs σ1 V1))])
          (cond
            [(or (.//? Vi) (.μ/V? Vi))
             (match V1
               [(.L i) (cons (σ-set σ1 i Vi) V1)]
               [_ (cons σ1 Vi)])]
            [else (error "⊕: impossible")]))]
       [((? list? V0) (? list? V1))
        (match-let ([(cons σ1′ l-rev)
                     (for/fold ([acc : (Pairof .σ (Listof .V)) (cons σ1 '())]) ([V0i V0] [V1i V1])
                       (match-let* ([(cons σ1 l) acc]
                                    [(cons σ1′ Vi) (⊕ σ0 V0i σ1 V1i)])
                         (cons σ1′ (cons Vi l))))])
          (cons σ1′ (reverse l-rev)))])]
    [(σ0 σ1 F)
     (for/fold : .σ ([σ1 : .σ σ1]) ([i (in-hash-keys F)])
       (let* ([j (hash-ref F i)])
         (match (⊕ (V-abs σ0 (σ@ σ0 i)) (V-abs σ1 (σ@ σ1 i)))
           [(and V (or (? .//?) (? .μ/V?))) (σ-set σ1 j V)]
           [_ (error "⊕: impossible")])))]
    [(x y)
     (match* (x y)
       ; same-length lists expected
       [((? list? V0) (? list? V1)) (map ⊕ V0 V1)]
       ; values
       [((? .V? V0) (? .V? V1))
        #;(printf "⊕:~n~a~nand~n~a~n~n" (show-Ans σ∅ V0) (show-Ans σ∅ V1))
        #;(printf "⊕:~n~a~nand~n~a~n~n" V0 V1)
        (let: ([ans : .V (cond
          [(V∈ V1 V0) V1] ; postpone approximation if value shrinks
          #;[(and (.//? V1) (.•? (.//-pre V1)) (= 1 (set-count (.//-refine V1)))) V1]
          #;[(equal? V0 ♦) ♦]
          [(⊑ V1 V0) V0]
          [(⊑ V0 V1) V1]
          [else
           (match* (V0 V1)
             [((.// U0 C*) (.// U1 D*))
              (match* (U0 U1)
                ; keep around common values: 0, 1, #t, #f, struct with no component
                [(_ (or '• (? .o?) (.b 0) (.b 1) (.b #t) (.b #f) (.St _ '()))) V1]
                ; cannot blur higher order value
                [(_ (.λ↓ f ρ))
                 (let ([repeated (repeated-lambdas f ρ)])
                   (match (set-count repeated)
                     [0 V1]
                     ; TODO: μ introduced outside here. Am i sure there's none inside?
                     [_ (let ([V′ (μV raw:X (set-add repeated (for/fold ([V1 : .V V1]) ([Vi repeated])
                                                            (V/ V1 Vi (.X/V raw:X)))))])
                          #;(printf "~a~n⇒⊕~n~a~n~n" V1 V′)
                          V′)]))]
                [((.Ar C V0 l) (.Ar C V1 l))
                 (.// (.Ar C (⊕ V0 V1) l) D*)]
                [(_ (or (? .λ?) (? .Ar?))) V1]
                [((.St t V0*) (.St t V1*)) (.// (.St t (⊕ V0* V1*)) D*)]
                [(_ (.St t V1*)) #;(printf "⊕:case1~n")
                                 #;(printf "⊕:~n~a~nand~n~a~n~n" (show-E σ∅ V0) (show-E σ∅ V1))
                                 (match-let* ([x raw:X #;(fresh V1*)]
                                              [Vi* (V/ V1* V0 (.X/V x))]
                                              [(cons Vi* Vs) (elim-μ x Vi*)])
                                   (if (equal? Vi* V1*) (.// '• (set-intersect C* D*))
                                       #;(μV x (compact {set V0 (.// (.St t Vi*) D*)} Vs))
                                       (.// (.St t (V/ Vi* (.X/V x) (μV x (compact {set V0 (.// (.St t Vi*) ∅)} Vs)))) D*)))]
                [((.b (? number? b0)) (.b (? number? b1)))
                 (cond ; if it moves towards 0, let it take its time
                   #;[(and (integer? b0) (integer? b1) (or (<= 0 b1 b0) (>= 0 b1 b0))) V1]
                   [else
                    (.// '• (set-add
                             (cond [(and (real? b0) (real? b1))
                                    {set (cond [(and (> b0 0) (> b1 0)) POS/C]
                                               [(and (< b0 0) (< b1 0)) NEG/C]
                                               [(and (not (= b0 0)) (not (= b1 0))) NON-ZERO/C]
                                               [(and (>= b0 0) (>= b1 0)) NON-NEG/C]
                                               [(and (<= b0 0) (<= b1 0)) NON-POS/C]
                                               [else REAL/C])}]
                                   [else ∅])
                             (cond [(and (integer? b0) (integer? b1)) INT/C]
                                   [(and (real? b0) (real? b1)) REAL/C]
                                   [else NUM/C])))])]
                [(_ _)
                 (let ([C* (set-union C* (raw:U^ U0))])
                   (.// '• (for/set: : (Setof .V) ([D (set-union D* (raw:U^ U1))]
                                                   #:when (eq? '✓ (C*⇒C C* D)))
                             D)))])]
             [((.μ/V x V0*) (.μ/V y V1*)) #;(printf "⊕:case2~n") (μV x (compact V0* (V/ V1* (.X/V y) (.X/V x))))]
             [((.μ/V x V0*) _)
              #;(printf "⊕:case3~n")
              #;(printf "~a  ∩  ~a~n~n" (v-class σ∅ V0*) (v-class σ∅ V1))
              (if (set-empty? (set-intersect (v-class σ∅ V0*) (v-class σ∅ V1)))
                  V1
                  (match-let ([(cons V1′ Vs) (dbg/off 'case3 (elim-μ x (V/ V1 V0 (.X/V x))))])
                (μV x (dbg/off 'compact1 (compact (dbg/off 'compact0 (compact V0* {set V1′})) Vs)))))]
             [(_ (.μ/V x V1*))
              #;(printf "⊕:case4~n")
              #;(printf "~a  ∩  ~a~n~n" (v-class σ∅ V0) (v-class σ∅ V1*))
              (if (set-empty? (set-intersect (v-class σ∅ V0) (v-class σ∅ V1*)))
                  V1
                  (match-let ([(cons V0′ Vs) (elim-μ x (V/ V0 V1 (.X/V x)))])
                    (μV x (compact (compact {set V0′} Vs) V1*))))]
             [((? .X/V? x) _) x]
             [(_ (? .X/V? x)) x])])])
          #;(printf "⊕:~n~a~nand~n~a~nis~n~a~n~n" (show-Ans σ∅ V0) (show-Ans σ∅ V1) (show-Ans σ∅ ans))
          (check ans)
          ans)]
       [((and ρ0 (.ρ m0 l0)) (and ρ1 (.ρ m1 l1)))
        (let* ([l (max l0 l1)]
               [m (for/fold ([m : (Map (U Integer Identifier) .V) (hash)]) ([sd (in-range 0 l)])
                    (match* ((hash-ref m0 (- l0 sd 1) (λ () #f))
                             (hash-ref m1 (- l1 sd 1) (λ () #f)))
                      [(#f #f) m]
                      [(#f (? .V? V)) (hash-set m (- l sd 1) V)]
                      [((? .V? V) #f) (hash-set m (- l sd 1) V)]
                      [((? .V? V0) (? .V? V1)) (hash-set m (- l sd 1) (⊕ V0 V1))]))]
               [m (for/fold ([m : (Map (U Integer Identifier) .V) m])
                            ([k (in-hash-keys m0)] #:when (symbol? k))
                    (hash-set m k (hash-ref m0 k)))]
               [m (for/fold ([m : (Map (U Integer Identifier) .V) m])
                            ([k (in-hash-keys m1)] #:when (symbol? k))
                    (hash-set m k (hash-ref m1 k)))])
          (.ρ m l))])]))

(: check : (case→ [.V → Void]
                  [.V Integer → Void]))
(define (check V [i 1])
  (match V
    [(.μ/V _ V*) (if (<= i 0) (error "no!") (for ([Vi V*]) (check Vi (- i 1))))]
    [(.// (.St _ V*) _) (for ([Vi V*]) (check Vi))]
    [_ (void)]))

;; remove all sub-μ. TODO: generalize allowed μ-depth
(: elim-μ : (case→ [Identifier .V → (Pairof .V (Setof .V))]
                   [Identifier (Listof .V) → (Pairof (Listof .V) (Setof .V))]))
(define (elim-μ x V)
  (define-set bodies : .V)
  (: go : (case→ [.V → .V] [(Listof .V) → (Listof .V)]))
  (define go
    (match-lambda
      [(? list? V*) (map go V*)]
      [(? .L? V) V]
      [(and V (.// U1 C*))
       (match U1
         [(.St t V*) (.// (.St t (map go V*)) C*)]
         [(.Ar C V l) (.// (.Ar C (go V) l) C*)]
         [(.λ↓ f (and ρ (.ρ m l)))
          #;(printf "elim-μ: ρ:~n~a~n~n" m)
          (let ([m′ (for/fold ([m′ : (Map (U Integer Identifier) .V) m∅])
                              ([x (in-hash-keys m)])
                      (hash-set m′ x (go (hash-ref m x))))])
            (if (equal? m′ m) V (.// (.λ↓ f (.ρ m′ l)) C*)))]
         [_ V])]
      [(.μ/V z V*) (bodies-add! (for/set: : (Setof .V) ([Vi V*]) (V/ Vi (.X/V z) (.X/V x)))) (.X/V x)]
      [(.X/V _) (.X/V x)]))
  
  (let ([V′ (go V)])
    #;(printf "elim-μ depth ~a → ~a~n~n" (μ-depth V) (μ-depth V′))
    (cons V′ bodies)))

;; remove redundant variable
;; simplify to • if body has •
(: μV : Identifier (Setof .V) → .V)
(define (μV x V*)
  #;(for ([Vi V*]) (check Vi 0))
  (let ([V* (for/set: : (Setof .V) ([V V*] #:unless (equal? V (.X/V x))) V)])
    (cond
      [(set-member? V* ♦) ♦]
      [else (match (set-count V*)
              [0 V∅]
              [1 (let* ([V (set-first V*)]
                        [V′ (V/ V (.X/V x) (.X/V #'☠))])
                   (if (equal? V V′) V V∅))]
              [_ (.μ/V x V*)])])))

; group values together by top constructors
(: compact : (Setof .V) (Setof .V) → (Setof .V))
(define (compact V0s V1s)
  #;(printf "compact:~n~n~a~nand~n~a~n~n~n" V0s V1s)
  #;(printf "depth: ~a, ~a~n~n"
          (for/list: : (Listof Integer) ([V V0s]) (μ-depth V))
          (for/list: : (Listof Integer) ([V V1s]) (μ-depth V)))
  (: collect : (Setof .V) → (Values (Map Any .V) (Setof .X/V)))
  (define (collect Vs)
    #;(printf "collect:~n~a~n~n" Vs)
    (for/fold ([m : (Map Any .V) (hash)] [xs : (Setof .X/V) ∅]) ([V Vs])
      (match V
        [(.// U C*)
         (match U
           [(.b (? number?)) (values (hash-set m 'number? V) xs)]
           [(.b (? string?)) (values (hash-set m 'string? V) xs)]
           [(.b (? symbol?)) (values (hash-set m 'symbol? V) xs)]
           [(.b #t) (values (hash-set m #t V) xs)]
           [(.b #f) (values (hash-set m #f V) xs)]
           [(? .o? o) (values (hash-set m `(o ,(name o)) V) xs)]
           ['• (values (hash-set m (for/fold : Any ([ac : Any '•]) ([C C*])
                                     (match C
                                       [(.// (? .pred? p) _) (match p
                                                               [(.st-p t _) t]
                                                               [_ (name p)])]
                                       [_ ac]))
                                 V)
                       xs)]
           [(or (? .Ar?) (? .λ↓?) (? .o?)) (values (hash-set m 'proc? V) xs)] ; TODO: by arity also?
           [(.St t _) (values (hash-set m `(struct ,t) V) xs)])]
        [(? .μ/V? V) (error (format "weird:~n~a~n~a~n~n" V0s V1s)) (values (hash-set m 'μ V) xs)]
        [(? .X/V? x) (values m (set-add xs x))])))
  
  (: merge : (.V .V → (Pairof .V (Setof .V))))
  (define (merge V0 V1)
    (match* (V0 V1)
      [((? .X/V? x) V1) (cons x (match V1 [(.X/V _) ∅] [_ {set V1}]))]
      [((.// (.St t V0*) C*) (.// (.St t V1*) D*))
       (let-values ([(q V*)
                     (for/fold ([q : (Setof .V) ∅] [V* : (Listof .V) '()]) ([Vi V0*] [Vj V1*])
                       (match-let ([(cons V′ q′) (merge Vi Vj)])
                         (values (set-union q q′) (cons V′ V*))))])
         (cons (.// (.St t (reverse V*)) (set-intersect C* D*)) q))]
      [(_ _) (match (⊕ V0 V1) ; FIXME hack
               [(and V (.μ/V x V*)) (elim-μ x V)]
               [V (cons V ∅)])]))  
  
  (: go : (Setof .V) (Setof .V) → (Setof .V))
  (define (go V0s V1s)
    #;(printf "go:~n~a~n~nand~n~n~a~n~n~n" V0s V1s)
    (let-values ([(m0 xs) (collect V0s)]
                 [(m1 zs) (collect V1s)])
      (let: ([q : (Setof .V) ∅])
        (let ([s0 (for/set: : (Setof .V) ([k (in-hash-keys m0)])
                    (let ([V0 (hash-ref m0 k)])
                      (match (hash-ref m1 k (λ () #f))
                        [#f V0]
                        [(? .V? V1) (match-let ([(cons V′ q′) (dbg/off 'go (merge V0 V1))])
                                      (set! q (set-union q q′))
                                      V′)])))]
              [s1 (for/set: : (Setof .V) ([k (in-hash-keys m1)] #:unless (hash-has-key? m0 k))
                    (hash-ref m1 k))])
          (let* ([s (set-union s0 s1)])
            (if (subset? q s) s
                (begin #;(printf "q: ~a~n~ns:~a~n~n"
                               (for/set: : (Setof Any) ([x q]) (show-V σ∅ x))
                               (for/set: : (Setof Any) ([x s]) (show-V σ∅ x)))
                       (go s q))))))))
  
  (go V0s V1s))

(: μ-depth : (case→ [.V → Integer] [(Listof .V) → (Listof Integer)]))
(define μ-depth
  (match-lambda
    [(? list? V*) (map μ-depth V*)]
    [(.// (.St _ V*) _) (apply max (map μ-depth V*))]
    [(.μ/V _ V*) (+ 1 (for/fold : Integer ([l 0]) ([V V*]) (max l (μ-depth V))))]
    [(? .V?) 0]))

(: refine-V : .V .V → .V)
(define (refine-V V C)
  (match-let* ([(cons σ V) (raw:alloc σ∅ V)]
               [(cons σ V) (refine1 σ V C)])
    (V-abs σ V)))

(: reify : .V → .V)
(define (reify C)
  (match C
    [(.L _) (.// '• {set C})]
    [(.// Uc _)
     (match Uc
       [(.St 'and/c (list C1 C2)) (refine-V (reify C1) C2)]
       [(.St 'or/c (list C1 C2))
        (match* ((reify C1) (reify C2))
          [((.μ/V x V1*) (.μ/V z V2*)) (μV x {set-union V1* (V/ V2* (.X/V z) (.X/V x))})]
          [((and V1 (.μ/V x V1*)) V2) (μV x (set-add V1* (V/ V2 V1 (.X/V x))))]
          [(V1 (and V2 (.μ/V x V2*))) (μV x (set-add V2* (V/ V1 V2 (.X/V x))))]
          [(V1 V2) (if (equal? V1 V2) V1 (μV raw:X {set V1 V2}))])]
       [(.St/C t D*) (→V (.St t (map reify D*)))]
       [(.μ/C x D) (match (reify D)
                     [(.μ/V '_ V*) (μV x V*)]
                     [(? .V? V) V])]
       [(and Uc (.Λ/C C* D v?)) (→V (.Ar (→V Uc) ♦ `(Λ Λ Λ) #|FIXME|#))]
       [(.X/C x) (.X/V x)]
       [(.st-p t n) (→V (.St t (make-list n ♦)))]
       [(.λ↓ (.λ 1 (.b #t)) _) ♦]
       [_ (.// '• {set (simplify C)})])]))
