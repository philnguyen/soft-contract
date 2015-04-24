#lang typed/racket/base
(require racket/match racket/set racket/list racket/function racket/bool
         "../utils.rkt" "../lang.rkt" "../runtime.rkt" "../provability.rkt" "../show.rkt"
         (prefix-in raw: "../delta.rkt"))
(provide δ ⊕ ⊕* ⊕/σ ⊕/V refine alloc refine1)

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
  (parameterize ([raw:refine1 refine1])
    (let ([C (simplify C)])
      #;(log-debug "refine1:~n~a~n~a~n~a~n~n" (show-σ σ) (show-E σ V) (show-E σ C))
      (when (match? C (.// '• _)) (error "ha!"))
      (match V
        [(.L i) (match-let ([(cons σ′ V′) (refine1 σ (σ@ σ i) C)])
                  (match V′
                    [(.// (.St t V*) C*) (match-let* ([(cons σ′ V*′) (raw:alloc σ′ V*)]
                                                      [V′ (.// (.St t V*′) C*)])
                                           (cons (σ-set σ′ i V′) V))]
                    [(? .//? V′) (cons (σ-set σ′ i V′) V)]
                    [(? .μ/V? V′) (cons (σ-set σ′ i V′) V)] ; duplicate to get around TR
                    [_ (error "broken =_=" V)]))]
      [(.// U C*)
       (match C
         [(.L _) (cons σ (.// U (set-add C* C)))]
         [(.// Uc _)          
          (match Uc
            [(.St (.id 'and/c 'Λ) (list C1 C2)) (raw:refine σ V C1 C2)]
            [(.St (.id 'or/c 'Λ) (list C1 C2))
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
                                   (cons σ (.// (raw:U+ U U′) (raw:∪* C* C*′ C))))]
                         [(.// U′ C*′) (cons σ (.// (raw:U+ U U′) (raw:∪* C* C*′)))])]
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
                           [(.St (? (curry equal? t)) _) (cons σ V)])]
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
                          ['?
                           (match-define (cons σ′ Vj) (refine1 σ Vi C))
                           (define-values (Vj′ Vs′) (elim-μ x Vj))
                           (values σ′ (compact (compact Vs Vs′) {set Vj′}))]))])
         #;(log-debug "new V* is ~a~n~n" (for/set: Any ([Vi V*′]) (show-V σ′ Vi)))
         (match (set-count V*′)
           [0 (error "bogus refinement") #;V∅]
           [1 (cons σ′ (V/ (set-first V*′) (.X/V x) V))]
           [_ (cons σ′ (μV x V*′))]))]
       [(? .X/V? x) (cons σ x)])))) ; abuse μ for non-inductive set

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
                      [(false? u) 'false?]
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

(: ⊕ : .σ .V .σ .V → (Pairof .σ .V))
(define (⊕ σ₀ V₀ σ₁ V₁)
  (parameterize ([raw:refine1 refine1])
    (define Vᵢ (⊕/V (V-abs σ₀ V₀) (V-abs σ₁ V₁)))
    (match V₁
      [(.L i)
       (match-let ([(cons σ₁* Vᵢ*) (raw:alloc σ₁ Vᵢ)])
         (match Vᵢ*
           [(.L j) (cons (σ-set σ₁* i (σ@ σ₁* j)) V₁)]
           [(and Vᵢ* (or (? .//?) (? .μ/V?))) (cons (σ-set σ₁* i Vᵢ*) V₁)]
           [_ (error 'Internal "impossible instance of .X/V in ⊕'s definition")]))]
      [_ (raw:alloc σ₁ Vᵢ)])))

(: ⊕* : .σ (Listof .V) .σ (Listof .V) → (Pairof .σ (Listof .V)))
(define (⊕* σ₀ Vs₀ σ₁ Vs₁)
  (match-define (cons σ₁* l-rev)
    (for/fold ([acc : (Pairof .σ (Listof .V)) (cons σ₁ '())]) ([V₀ Vs₀] [V₁ Vs₁])
      (match-define (cons σ₁ l) acc)
      (match-define (cons σ₁* Vᵢ) (⊕ σ₀ V₀ σ₁ V₁))
      (cons σ₁* (cons Vᵢ l))))
  (cons σ₁* (reverse l-rev)))

(: ⊕/σ : .σ .σ .F → .σ)
(define (⊕/σ σ₀ σ₁ F)
  (parameterize ([raw:refine1 refine1])
    (for/fold ([σ₁ : .σ σ₁]) ([(i j) (in-hash F)])
      (match (⊕/V (V-abs σ₀ (σ@ σ₀ i)) (V-abs σ₁ (σ@ σ₁ i)))
        [(and V (or (? .//?) (? .μ/V?))) (σ-set σ₁ j V)]
        [_ (error 'Internal "impossible instance of .X/V in ⊕/σ's definition")]))))

(: ⊕/ρ : .ρ .ρ → .ρ)
(define (⊕/ρ ρ₀ ρ₁)
  (match-define (.ρ m₀ l₀) ρ₀)
  (match-define (.ρ m₁ l₁) ρ₁)
  (define l (max l₀ l₁))
  (define m
    (for/fold ([m : (Map (U Integer Symbol) .V) (hash)]) ([sd (in-range 0 l)])
      (match* ((hash-ref m₀ (- l₀ sd 1) #f) (hash-ref m₁ (- l₁ sd 1) #f))
        [(#f #f) m]
        [(#f (? .V? V)) (hash-set m (- l sd 1) V)]
        [((? .V? V) #f) (hash-set m (- l sd 1) V)]
        [((? .V? V₀) (? .V? V₁)) (hash-set m (- l sd 1) (⊕/V V₀ V₁))])))
  (define m*
    (for/fold ([m : (Map (U Integer Symbol) .V) m])
              ([(k v) (in-hash m₀)] #:when (symbol? k))
      (hash-set m k v)))
  (define m**
    (for/fold ([m : (Map (U Integer Symbol) .V) m*])
              ([(k v) (in-hash m₁)] #:when (symbol? k))
      (hash-set m k v)))
  (.ρ m** l))

(: ⊕/V : .V .V → .V)
(define (⊕/V V₀ V₁)
  ;;(log-debug "⊕:~n~a~nand~n~a~n~n" (show-Ans σ∅ V0) (show-Ans σ∅ V1))
  ;;(log-debug "⊕:~n~a~nand~n~a~n~n" V0 V1)
  (cond
    [(V∈ V₁ V₀) V₁] ; postpone approximation if value shrinks
    ;;[(and (.//? V1) (.•? (.//-pre V1)) (= 1 (set-count (.//-refine V1)))) V1]
    ;;[(equal? V0 ♦) ♦]
    [(⊑/V V₁ V₀) V₀]
    [(⊑/V V₀ V₁) V₁]
    [else
     (match* (V₀ V₁)
       [((.// U₀ Cs) (.// U₁ Ds))
        (match* (U₀ U₁)
          ; keep around common values: 0, 1, #t, #f, struct with no component
          [(_ (or '• (? .o?) (.b 0) (.b 1) (.b #t) (.b #f) (.St _ '()))) V₁]
          ; cannot blur higher order value
          [(_ (.λ↓ f ρ))
           (define repeated (repeated-lambdas f ρ))
           (match (set-count repeated)
             [0 V₁]
             [_ ; TODO: μ introduced outside here. Am i sure there's none inside?
              (μV 'X (set-add repeated
                              (for/fold ([V₁ : .V V₁]) ([Vᵢ repeated])
                                (V/ V₁ Vᵢ (.X/V 'X)))))])]
          [((.Ar C V₀ l) (.Ar C V₁ l))
           (.// (.Ar C (⊕/V V₀ V₁) l) Ds)]
          [(_ (or (? .λ?) (? .Ar?))) V₁]
          [((.St t Vs₀) (.St t Vs₁)) (.// (.St t (map ⊕/V Vs₀ Vs₁)) Ds)]
          [(_ (.St t Vs₁))
           ;;(log-debug "⊕:case1~n")
           ;;(log-debug "⊕:~n~a~nand~n~a~n~n" (show-E σ∅ V0) (show-E σ∅ V1))
           (define x 'X #;(fresh V1*))
           (define Vsᵢ (V/ Vs₁ V₀ (.X/V x)))
           (define-values (Vsᵢ* Vs) (elim-μ x Vsᵢ))
           (cond
             [(equal? Vsᵢ* Vs₁) (.// '• (set-intersect Cs Ds))]
             ;;(μV x (compact {set V0 (.// (.St t Vi*) D*)} Vs))
             [else
              (.// (.St t (V/ Vsᵢ (.X/V x) (μV x (compact {set V₀ (.// (.St t Vsᵢ) ∅)} Vs)))) Ds)])]
          [((.b (? number? b₀)) (.b (? number? b₁)))
           (cond ; if it moves towards 0, let it take its time
             ;;[(and (integer? b₀) (integer? b₁) (or (<= 0 b₁ b₀) (>= 0 b₁ b₀))) V1]
             [else
              (.// '• (set-add
                       (cond [(and (real? b₀) (real? b₁))
                              {set (cond [(and (> b₀ 0) (> b₁ 0)) POS/C]
                                         [(and (< b₀ 0) (< b₁ 0)) NEG/C]
                                         [(and (not (= b₀ 0)) (not (= b₁ 0))) NON-ZERO/C]
                                         [(and (>= b₀ 0) (>= b₁ 0)) NON-NEG/C]
                                         [(and (<= b₀ 0) (<= b₁ 0)) NON-POS/C]
                                         [else REAL/C])}]
                             [else ∅])
                       (cond [(and (integer? b₀) (integer? b₁)) INT/C]
                             [(and (real? b₀) (real? b₁)) REAL/C]
                             [else NUM/C])))])]
          [(_ _)
           (define Cs* (set-union Cs (raw:U^ U₀)))
           (.// '• (for/set: : (Setof .V) ([D (set-union Ds (raw:U^ U₁))]
                                           #:when (eq? '✓ (C*⇒C Cs* D)))
                     D))])]
       [((.μ/V x Vs₀) (.μ/V y Vs₁))
        ;;(log-debug "⊕:case2~n")
        (μV x (compact Vs₀ (V/ Vs₁ (.X/V y) (.X/V x))))]
       [((.μ/V x Vs₀) _)
        ;;(log-debug "⊕:case3~n")
        ;;(log-debug "~a  ∩  ~a~n~n" (v-class σ∅ V0*) (v-class σ∅ V1))
        (cond
          [(set-empty? (∩ (v-class σ∅ Vs₀) (v-class σ∅ V₁))) V₁]
          [else
           (define-values (V₁* Vs) (elim-μ x (V/ V₁ V₀ (.X/V x))))
           (μV x (compact (compact Vs₀ {set V₁*}) Vs))])]
       [(_ (.μ/V x Vs₁))
        ;;(log-debug "⊕:case4~n")
        ;;(log-debug "~a  ∩  ~a~n~n" (v-class σ∅ V0) (v-class σ∅ V1*))
        (cond
          [(set-empty? (∩ (v-class σ∅ V₀) (v-class σ∅ Vs₁))) V₁]
          [else
           (define-values (V₀* Vs) (elim-μ x (V/ V₀ V₁ (.X/V x))))
           (μV x (compact (compact {set V₀*} Vs) Vs₁))])]
       [((? .X/V? x) _) x]
       [(_ (? .X/V? x)) x])]))

;; remove all sub-μ. TODO: generalize allowed μ-depth
(: elim-μ : (case-> [Symbol .V → (Values .V (Setof .V))]
                    [Symbol (Listof .V) → (Values (Listof .V) (Setof .V))]))
(define (elim-μ x V)
  (define-set bodies : .V)
  
  (: go! : .V → .V)
  (define go!
    (match-lambda
      [(? .L? V) V]
      [(and V (.// U1 Cs))
       (match U1
         [(.St t Vs) (.// (.St t (go*! Vs)) Cs)]
         [(.Ar C V l) (.// (.Ar C (go! V) l) Cs)]
         [(.λ↓ f (and ρ (.ρ m l)))
          #;(log-debug "elim-μ: ρ:~n~a~n~n" m)
          (define m*
            (for/fold ([m* : (Map (U Integer Symbol) .V) m∅])
                      ([(x v) (in-hash m)])
              (hash-set m* x (go! v))))
          (if (equal? m* m) V (.// (.λ↓ f (.ρ m* l)) Cs))]
         [_ V])]
      [(.μ/V z V*) (bodies-union! (for/set: : (Setof .V) ([Vi V*]) (V/ Vi (.X/V z) (.X/V x)))) (.X/V x)]
      [(.X/V _) (.X/V x)]))

  (: go*! : (Listof .V) → (Listof .V))
  (define (go*! xs) (map go! xs))

  (cond
    [(.V? V) (define V* (go! V)) (values V* bodies)]
    [else (define V* (go*! V)) (values V* bodies)]))

;; remove redundant variable
;; simplify to • if body has •
(: μV : Symbol (Setof .V) → .V)
(define (μV x Vs)
  (define Vs* (for/set: : (Setof .V) ([V Vs] #:unless (equal? V (.X/V x))) V))
  (cond
    [(∋ Vs* ♦) ♦]
    [else (match (set-count Vs*)
            [0 V∅]
            [1
             (define V (set-first Vs*))
             (define V* (V/ V (.X/V x) (.X/V '☠)))
             (if (equal? V V*) V V∅)]
            [_ (.μ/V x Vs*)])]))

; group values together by top constructors
(: compact : (Setof .V) (Setof .V) → (Setof .V))
(define (compact V0s V1s)
  #;(log-debug "compact:~n~n~a~nand~n~a~n~n~n" V0s V1s)
  #;(log-debug "depth: ~a, ~a~n~n"
          (for/list: : (Listof Integer) ([V V0s]) (μ-depth V))
          (for/list: : (Listof Integer) ([V V1s]) (μ-depth V)))
  (: collect : (Setof .V) → (Values (Map Any .V) (Setof .X/V)))
  (define (collect Vs)
    #;(log-debug "collect:~n~a~n~n" Vs)
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
  
  (: merge : .V .V → (Values .V (Setof .V)))
  (define (merge V0 V1)
    (match* (V0 V1)
      [((? .X/V? x) V1) (values x (match V1 [(.X/V _) ∅] [_ {set V1}]))]
      [((.// (.St t V0*) C*) (.// (.St t V1*) D*))
       (let-values ([(q V*)
                     (for/fold ([q : (Setof .V) ∅] [V* : (Listof .V) '()]) ([Vi V0*] [Vj V1*])
                       (define-values (V′ q′) (merge Vi Vj))
                       (values (set-union q q′) (cons V′ V*)))])
         (values (.// (.St t (reverse V*)) (set-intersect C* D*)) q))]
      [(_ _) (match (⊕/V V0 V1) ; FIXME hack
               [(and V (.μ/V x V*)) (elim-μ x V)]
               [V (values V ∅)])]))  
  
  (: go : (Setof .V) (Setof .V) → (Setof .V))
  (define (go V0s V1s)
    #;(log-debug "go:~n~a~n~nand~n~n~a~n~n~n" V0s V1s)
    (let-values ([(m0 xs) (collect V0s)]
                 [(m1 zs) (collect V1s)])
      (let: ([q : (Setof .V) ∅])
        (let ([s0 (for/set: : (Setof .V) ([k (in-hash-keys m0)])
                    (let ([V0 (hash-ref m0 k)])
                      (match (hash-ref m1 k (λ () #f))
                        [#f V0]
                        [(? .V? V1)
                         (define-values (V′ q′) (merge V0 V1))
                         (set! q (set-union q q′))
                         V′])))]
              [s1 (for/set: : (Setof .V) ([k (in-hash-keys m1)] #:unless (hash-has-key? m0 k))
                    (hash-ref m1 k))])
          (let* ([s (set-union s0 s1)])
            (if (subset? q s) s
                (begin #;(log-debug "q: ~a~n~ns:~a~n~n"
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
       [(.St (.id 'and/c 'Λ) (list C1 C2)) (refine-V (reify C1) C2)]
       [(.St (.id 'or/c 'Λ) (list C1 C2))
        (match* ((reify C1) (reify C2))
          [((.μ/V x V1*) (.μ/V z V2*)) (μV x {set-union V1* (V/ V2* (.X/V z) (.X/V x))})]
          [((and V1 (.μ/V x V1*)) V2) (μV x (set-add V1* (V/ V2 V1 (.X/V x))))]
          [(V1 (and V2 (.μ/V x V2*))) (μV x (set-add V2* (V/ V1 V2 (.X/V x))))]
          [(V1 V2) (if (equal? V1 V2) V1 (μV 'X {set V1 V2}))])]
       [(.St/C t D*) (→V (.St t (map reify D*)))]
       [(.μ/C x D) (match (reify D)
                     [(.μ/V '_ V*) (μV x V*)]
                     [(? .V? V) V])]
       [(and Uc (.Λ/C C* D v?)) (→V (.Ar (→V Uc) ♦ `(Λ Λ Λ) #|FIXME|#))]
       [(.X/C x) (.X/V x)]
       [(.st-p t n) (→V (.St t (make-list n ♦)))]
       [(.λ↓ (.λ 1 (.b #t)) _) ♦]
       [_ (.// '• {set (simplify C)})])]))
