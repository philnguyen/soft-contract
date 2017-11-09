#lang typed/racket/base

(provide val@)

(require typed/racket/unit
         racket/match
         racket/set
         racket/splicing
         set-extras
         "../utils/main.rkt"
         "../ast/signatures.rkt"
         "signatures.rkt")

(define-unit val@
  (import path^ pretty-print^ sto^)
  (export val^)

  (: fresh-sym! : → Integer)
  (define fresh-sym!
    (let ([n : Integer 0])
      (λ ()
        (begin0 n (set! n (+ 1 n))))))

  (: C-flat? : -V → Boolean)
  ;; Check whether contract is flat, assuming it's already a contract
  (define (C-flat? V)
    (match V
      [(-And/C flat? _ _) flat?]
      [(-Or/C flat? _ _) flat?]
      [(? -Not/C?) #t]
      [(? -One-Of/C?) #t]
      [(-St/C flat? _ _) flat?]
      [(or (? -Vectorof?) (? -Vector/C?)) #f]
      [(-Hash/C _ _) #f] ; TODO
      [(-Set/C _) #f] ; TODO
      [(? -=>_?) #f]
      [(or (? -Clo?) (? -Ar?) (? -prim?)) #t]
      [(? -x/C?) #t]
      [(? -∀/C?) #f]
      [(? -Seal/C?) #f]
      [V (error 'C-flat? "Unepxected: ~a" (show-V V))]))

  (: C^-flat? : -V^ → Boolean)
  (define (C^-flat? C^)
    (for/and : Boolean ([C (in-set C^)])
      (C-flat? C)))

  (splicing-local
      ((: with-swapper : (-l -ctx → -ctx) → -l -V → -V)
       (define ((with-swapper swap) l V)
         (match V
           [(-Ar C α ctx)
            (-Ar C α (swap l ctx))]
           [(-St* grd α ctx)
            (-St* grd α (swap l ctx))]
           [(-Vector/guard grd α ctx)
            (-Vector/guard grd α (swap l ctx))]
           [(-Hash/guard C α ctx)
            (-Hash/guard C α (swap l ctx))]
           [(-Set/guard C α ctx)
            (-Set/guard C α (swap l ctx))]
           [_ V])))
    (define with-negative-party
      (with-swapper
        (match-lambda**
          [(l (-ctx l+ _ lo ℓ))
           (-ctx l+ l lo ℓ)])))
    (define with-positive-party
      (with-swapper
        (match-lambda**
          [(l (-ctx _ l- lo ℓ))
           (-ctx l l- lo ℓ)]))))

  (: behavioral? : -σ -δσ -V → Boolean)
  ;; Check if value maybe behavioral.
  ;; `#t` is a conservative answer "maybe yes"
  ;; `#f` is a strong answer "definitely no"
  (define (behavioral? σ δσ V)
    (define-set seen : ⟪α⟫ #:eq? #t #:as-mutable-hash? #t)

    (: check-⟪α⟫! : ⟪α⟫ → Boolean)
    (define (check-⟪α⟫! ⟪α⟫)
      (cond [(seen-has? ⟪α⟫) #f]
            [else
             (seen-add! ⟪α⟫)
             (for/or ([V (in-set (σ@ σ δσ ⟪α⟫))])
               (check! V))]))

    (: check! : -V → Boolean)
    (define (check! V)
      (match V
        [(-St _ αs) (ormap check-⟪α⟫! αs)]
        [(-St* _ α _) (check-⟪α⟫! α)]
        [(-Vector αs) (ormap check-⟪α⟫! αs)]
        [(-Vector^ α _) (check-⟪α⟫! α)]
        [(-Ar grd α _) #t]
        [(-=> doms rngs)
         (match doms
           [(? list? doms)
            (or (for/or : Boolean ([dom (in-list doms)])
                  (check-⟪α⟫! (-⟪α⟫ℓ-addr dom)))
                (and (pair? rngs)
                     (for/or : Boolean ([rng (in-list rngs)])
                       (check-⟪α⟫! (-⟪α⟫ℓ-addr rng)))))]
           [(-var doms dom)
            (or (check-⟪α⟫! (-⟪α⟫ℓ-addr dom))
                (for/or : Boolean ([dom (in-list doms)])
                  (check-⟪α⟫! (-⟪α⟫ℓ-addr dom)))
                (and (pair? rngs)
                     (for/or : Boolean ([rng (in-list rngs)])
                       (check-⟪α⟫! (-⟪α⟫ℓ-addr rng)))))])]
        [(? -=>i?) #t]
        [(-Case-> cases) (ormap check! cases)]
        [(or (? -Clo?) (? -Case-Clo?)) #t]
        [_ #f]))

    (check! V))

  (define guard-arity : (-=>_ → Arity)
    (match-lambda
      [(-=> αs _) (shape αs)]
      [(and grd (-=>i αs (cons mk-D _)))
       (match mk-D
         [(-Clo xs _ _) (shape xs)]
         [_
          ;; FIXME: may be wrong for var-args. Need to have saved more
          (length αs)])]
      [(-Case-> cases) (normalize-arity (map guard-arity cases))]
      [(? -∀/C?)
       ;; TODO From observing behavior in Racket. But this maybe unsound for proof system
       (arity-at-least 0)]))

  (: blm-arity : ℓ -l Arity (Listof -V^) → -blm)
  (define blm-arity
    (let ([arity->msg : (Arity → Symbol)
                      (match-lambda
                        [(? integer? n)
                         (format-symbol (case n
                                          [(0 1) "~a value"]
                                          [else "~a values"])
                                        n)]
                        [(arity-at-least n)
                         (format-symbol "~a+ values" n)])])
      (λ (ℓ lo arity Vs)
        (blm/simp (ℓ-src ℓ) lo (list (arity->msg arity)) Vs ℓ))))

  (: predicates-of-V : -V → (℘ -h))
  (define predicates-of-V
    (match-lambda
      [(-b (? number?)) {set 'number?}]
      [(-b (? null?)) {set 'null?}]
      [(-b #f) {set 'not}]
      [(and b (-b (? symbol? s))) {set b}]
      #;[(-Clo _ ⟦e⟧ _) {set (-clo ⟦e⟧)}]
      [(or (-St 𝒾 _) (-St* (-St/C _ 𝒾 _) _ _)) #:when 𝒾 {set (-st-p 𝒾)}]
      [(or (? -Ar?) (? -o?)) {set 'procedure?}]
      [(-● ps) ps]
      [_ ∅]))

  (: V+ : -V^ (U -h -V) → -V^)
  (define V+
    (match-lambda**
     [((-● ps) (? -h? C)) (-● (set-add ps C))]
     [(V _) V]))

  (: estimate-list-lengths : -σ -δσ -V → (℘ (U #f Arity)))
  ;; Estimate possible list lengths from the object language's abstract list
  (define (estimate-list-lengths σ δσ V)
    (define-set seen : ⟪α⟫ #:eq? #t #:as-mutable-hash? #t)
    (define maybe-non-proper-list? : Boolean #f)

    (: arity-inc : Arity → Arity)
    (define arity-inc
      (match-lambda
        [(? exact-integer? n) (+ 1 n)]
        [(arity-at-least n) (arity-at-least (+ 1 n))]))
    
    (: go! : -V → (℘ Arity))
    (define go!
      (match-lambda
        [(-Cons _ αₜ)
         (cond [(seen-has? αₜ) {set (arity-at-least 0)}]
               [else (seen-add! αₜ)
                     (for/union : (℘ Arity) ([V* (in-set (σ@ σ δσ αₜ))])
                       (map/set arity-inc (go! V*)))])]
        [(-b '()) {set 0}]
        [(-● ps) #:when (∋ ps 'list?) {set (arity-at-least 0)}]
        [_ (set! maybe-non-proper-list? #t)
           ∅]))
    (define res
      (match (normalize-arity (set->list (go! V)))
        [(? list? l) (list->set l)]
        [a {set a}]))
    (if maybe-non-proper-list? (set-add res #f) res))

  )
