#lang racket
(require redex "utils.rkt")

(define-extended-language L MT
  ; source program syntax
  [(p q) (m ... e)]
  [m (def x v)]
  [e v x (e e) (o e ...) (if e e e)]
  [v (λ (x) e) b ⊤]
  [b #t #f n empty INT PROC]
  [o o1 o2]
  [o1 o? ac add1]
  [o2 cons * + - =]
  [o? int? false? cons? empty? proc? tt]
  [ac car cdr]
  [n integer]
  [(x y z X Y Z) variable-not-otherwise-mentioned]
  [(x* y* z* f* l*) (x ...)]
  [n• n INT]
  [n+⊤ n• ⊤]
  [PROC• PROC (⇓ (λ (x) e) ρ)]
  
  ; run-time configuration
  [P (m ... E)]
  [E A (: e ρ) (E E) (o E ...) (if E E E) (rt V V E)]
  [A (in-hole H Err) V]
  [A* (A ...)]
  [V (⇓ (λ (x) e) ρ) (Cons V V) b ⊤ ⊥]
  [V* (V ...)]
  [ρ ([x ↦ V] ...)]
  [ac* (ac ...)]
  
  ; evaluation context
  [H hole (H E) (V H) (o V ... H E ...) (if H E E) (rt V V H)]
  [Q (m ... H)]
  
  [P+Q P Q]
  [B #t #f])

(define-extended-language L∘ L
  [E .... (blur V E) (H* (in-hole H ◇) E)]
  [H .... (blur V H) (H* (in-hole H ◇) H)]
  [V .... (! X) (μ (X) V*)])

(define (ev t)
  (list->set (map last (apply-reduction-relation* ↦ (term (inj ,t))))))
(define (ev∘ t)
  (list->set (map last (apply-reduction-relation* ↦∘ (term (inj ,t))))))
(define (ev∘* t)
  (list->set (map last (apply-reduction-relation* ↦∘* (term (inj ,t))))))

(define (viz t)
  (traces ↦ (term (inj ,t))))
(define (viz∘ t)
  (traces ↦∘ (term (inj ,t))))
(define (viz∘* t)
  (traces ↦∘* (term (inj ,t))))

(define-metafunction L
  inj : p -> P
  [(inj (m ... e)) (m ... (: e {}))])

(define ↦
  (reduction-relation
   L
   #:domain P
   [==> (: v ρ) (close v ρ)  v]
   [==> (: x ρ) V
        x
        (where (any ... [x ↦ V] any_i ...) ρ)]
   [--> (m ... (in-hole H (: x ρ)))
        (m ... (in-hole H (close v {})))
        ref
        (where (any_1 ... (def x v) any_i ...) (m ...))]
   [==> (: (e_1 e_2) ρ) ((: e_1 ρ) (: e_2 ρ))  @-e]
   [==> (: (o e ...) ρ) (o (: e ρ) ...)  o-e]
   [==> (: (if e ...) ρ) (if (: e ρ) ...)  if-e]
   
   [==> (o V ...) A
        δ
        (where (any_1 ... A any_i ...) (δ o V ...))]
   [==> (if V E_1 E_2) E_1
        if-t
        (where (any_1 ... #f any_i ...) (δ false? V))]
   [==> (if V E_1 E_2) E_2
        if-f
        (where (any_1 ... #t any_i ...) (δ false? V))]
   [==> (rt V_f V_x V) V
        rt]
   [==> ((⇓ (λ (x) e) ρ) V) (: e (ρ+ ρ x V))  β]
   
   with
   [(--> (in-hole Q E_1) (in-hole Q E_2)) (==> E_1 E_2)]))

(define ↦∘
  (extend-reduction-relation
   ↦ L∘
   #:domain P+Q
   [--> (m ... (in-hole H ((⇓ (λ (x) e) ρ) V)))
        (m ... (in-hole H (rt (⇓ (λ (x) e) ρ) V (: e (ρ+ ρ x V)))))
        β
        (where [#f] (app-seen? H (⇓ (λ (x) e) ρ) V))]
   [--> (m ... (in-hole H ((⇓ (λ (x) e) ρ) V)))
        (m ... (in-hole H (rt (⇓ (λ (x) e) ρ) V_1 (: e (ρ+ ρ x V_1)))))
        β-axl
        (where V_0 (app-seen? H (⇓ (λ (x) e) ρ) V))
        (where V_1 (+: V_0 V))]
   [--> (m ... (in-hole H ((⇓ (λ (x) e) ρ) V)))
        (m ... (in-hole H (rt (⇓ (λ (x) e) ρ) V hole)))
        β-wait
        (where [#t] (app-seen? H (⇓ (λ (x) e) ρ) V))]))

(define ↦∘*
  (union-reduction-relations
   ↦∘
   (reduction-relation
    L∘
    #:domain P+Q
    [--> (m ... (in-hole H (rt V_f V_x E)))
         (m ... (in-hole H (rt V_f V_x (H* (in-hole H_k ◇) V))))
         jump
         (where (P+Q ...)
                ,(apply-reduction-relation* ↦∘ (term (m ... (rt V_f V_x E)))))
         (where (any_1 ... (m ... V) any_2 ...) (P+Q ...))
         (where (any_3 ... (m ... (in-hole H_k (rt V_f V_x hole))) any_4 ...) (P+Q ...))]
    [--> (in-hole Q (H* (in-hole H ◇) V))
         (in-hole Q V)
         H*-0]
    [--> (in-hole Q (H* (in-hole H ◇) V))
         (in-hole Q (H* (in-hole H ◇) (blur V (in-hole H V))))
         H*-1]
    [--> (in-hole Q (blur V_0 V_1))
         (in-hole Q (+: V_0 V_1))
         blur])))

;; ρ operations
(define-metafunction L∘
  ρ+ : ρ x V -> ρ
  [(ρ+ ρ x V) (env+ ρ x V)])
(define-metafunction L∘
  close : v ρ -> V
  [(close (λ (x) e) ρ) (⇓ (λ (x) e) ρ)]
  [(close v ρ) v])

;; checks whether current context results from given application
(define-metafunction L∘
  app-seen? : H V V -> [B] or V
  [(app-seen? (in-hole H (rt V_f V_x H_1)) V_f V_x) [#t]]
  [(app-seen? (in-hole H (rt V_f V_x H_1)) V_f V) V_x]
  [(app-seen? H V_f V) [#f]])

;; biased approximation
(define-metafunction L∘
  +: : V V -> V
  [(+: ⊥ V) V]
  [(+: V ⊥) V]
  [(+: V V) V]
  [(+: n•_1 n•_2) INT]
  [(+: (Cons V_1 V_2) (Cons V_3 V_4)) (Cons (+: V_1 V_2) (+: V_3 V_4))]
  [(+: (μ (X) V*) (μ (Y) {V ...})) (μ! (X) (+:: V*_1 {(V// V (! Y) (! X)) ...}))]
  [(+: (μ (X) V*) V) (μ! (X) (+:: V* (V// V (μ (X) V*) (! X))))]
  [(+: V_0 V_1)
   (μ! (X) {V_0 V_i})
   (where X ,(variable-not-in (term (V_0 V_1)) (term X)))
   (where V_i (V// V_1 V_0 (! X)))
   (side-condition (term (≠ V_i V_1)))]
  [(+: V_0 V_1) ⊤])

(define-metafunction L∘
  μ! : (X) V* -> V
  [(μ! (X) {any ... ⊤ any_1}) ⊤]
  [(μ! (X) V*) (μ (X) V*)])

(define-metafunction L∘
  +:: : V* V* -> V*
  [(+:: (V_1 ...) (V_2 ...))
   ,(match (term (+:* V_1 ... V_2 ...))
      [(list _ ... '⊤ _ ...) (term {⊤})]
      [V* (set->list (list->set V*))])])
(define-metafunction L∘
  +:* : V ... -> V*
  [(+:* (V_a ... ⊤ V_b ...)) {⊤}]
  [(+:* V) {V}]
  [(+:*) {}]
  [(+:* V V_a ... V V_b ...)
   (V V_r ...)
   (where (V_r ...) (+:* V_a ... V_b ...))]
  [(+:* n•_1 V_a ... n•_2 V_b ...)
   ((+: n•_1 n•_2) V_r ...)
   (where (V_r ...) (+:* V_a ... V_b ...))]
  [(+:* B_1 V_a ... B_2 V_b ...)
   (B_1 B_2 V_r ...)
   (where (V_r ...) (+:* V_a ... V_b ...))]
  [(+:* PROC•_1 V_a ... PROC•_2 V_b ...)
   ((+: PROC•_1 PROC•_2) V_r ...)
   (where (V_r ...) (+:* V_a ... V_b ...))]
  [(+:* V_1 V_a ... V_b ...)
   (V_1 V_r ...)
   (where (V_r ...) (+:* V_a ... V_b ...))]
  [(+:* (Cons V_1 V_2) V_a ... (Cons V_3 V_4) V_b ...)
   ((+: (Cons V_1 V_2) (Cons V_3 V_4)) V_r ...)
   (where (V_r ...) (+:* V_a ... V_b ...))])

;; closure substitution
(define-metafunction L∘
  V// : V V V -> V
  [(V// V_X V_X V_Y) V_Y]
  [(V// (μ (X) any) X V) (μ (X) any)]
  [(V// (Cons V_1 V_2) V_X V_Y) (Cons (V// V_1 V_X V_Y) (V// V_2 V_X V_Y))]
  [(V// V_Z V_X V_Y) V_Z])

(define-metafunction L∘
  δ : o V ... -> A*
  ; predicate
  [(δ tt V) {#t}]
  [(δ o? ⊤) {#t #f}]
  [(δ int? n•) {#t}]
  [(δ false? #f) {#t}]
  [(δ cons? (Cons V_1 V_2)) {#t}]
  [(δ empty? empty) {#t}]
  [(δ proc? PROC) {#t}]
  [(δ proc? (⇓ any any_ρ)) {#t}]
  [(δ o? V) {#f}]
  
  [(δ add1 n) (δ + 1 n)]
  
  [(δ car (Cons V_1 V_2)) {V_1}]
  [(δ cdr (Cons V_1 V_2)) {V_2}]
  [(δ ac ⊤) {⊤ Err}]
  [(δ ac V) {Err}]
  [(δ cons V_1 V_2) {(Cons V_1 V_2)}]
  
  [(δ + n_1 n_2) {,(+ (term n_1) (term n_2))}]
  [(δ + n• ...) {INT}]
  [(δ + n+⊤ ...) {INT Err}]
  
  [(δ - n_1 n_2) {,(- (term n_1) (term n_2))}]
  [(δ - n• ...) {INT}]
  [(δ - n+⊤ ...) {INT Err}]
  
  [(δ * n_1 n_2) {,(* (term n_1) (term n_2))}]
  [(δ * n•_1 ... 0 n•_2 ...) {0}]
  [(δ * n• ...) {INT}]
  [(δ * n+⊤ ...) {INT Err}]
  
  [(δ = n_1 n_2) {,(= (term n_1) (term n_2))}]
  [(δ = n•_1 n•_2) {#t #f}]
  [(δ = n+⊤_1 n+⊤_2) {#t #f Err}]
  
  [(δ o V ...) {Err}])

;; Examples
(define p-fac
  (term
   ((def fac
      (λ (n) (if (= n 0) 1 (* n (fac (- n 1))))))
    (fac INT))))
(define p-fg
  (term
   ((def f
      (λ (n) (if ⊤ 1 (+ (g n) (f n)))))
    (def g
      (λ (n) (if ⊤ 2 (+ (f n) (g n)))))
    (f INT))))
(define p-ack
  (term
   ((def ack
      (λ (m)
        (λ (n)
          (if (= m 0) (+ n 1)
              (if (= n 0) ((ack (- m 1)) 1)
                  ((ack (- m 1)) ((ack m) (- n 1))))))))
    ((ack INT) INT))))
(define p-fib
  (term
   ((def fib
      (λ (n)
        (if ⊤ 1 (+ (fib (- n 1)) (fib (- n 2))))))
    (fib INT))))
(define p-app
  (term
   ((def app
      (λ (xs)
        (λ (ys)
          (if (empty? xs) ys
              (cons (car xs) ((app (cdr xs)) ys))))))
    ((app ⊤) ⊤))))