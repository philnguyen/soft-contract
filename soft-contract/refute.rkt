#lang typed/racket/base

(provide refute-files)

(require
 racket/match racket/set
 "utils/set.rkt" "utils/map.rkt" "utils/untyped-macros.rkt"
 "ast/definition.rkt" "ast/meta-functions.rkt" "parse/main.rkt"
 "runtime/val.rkt" "runtime/addr.rkt" "runtime/path-inv.rkt" "runtime/store.rkt" "runtime/simp.rkt"
 "proof-relation/main.rkt" "proof-relation/ext/z3.rkt" "proof-relation/local.rkt"
 "delta.rkt"
 "reduction/step-app.rkt" "reduction/main.rkt"
 "machine/definition.rkt" "machine/load.rkt")

(: refute-files : Path-String * → (Option (Pairof -blm (Option -e))))
;; Read in modules and try to find a counterexample
(define (refute-files . paths)
  (parameterize ([Γ⊢ₑₓₜ z3⊢]
                 [↦opq ↦opq/ce]
                 [concrete? #t])
    (with-concrete-allocation
      (run (files->modules paths)))))

(: run : (Listof -module) → (Option (Pairof -blm (Option -e))))
;; Execute module list and return first counterexample (TODO generalize)
(define (run ms)
  (define-values (ς₀ e†) (𝑰 ms init-prim))
  (cond
    [(search {set ς₀}) =>
     (match-lambda
       [(list blm Γ mappings)
        (cons blm (and mappings (concretize-e Γ mappings e†)))])]
    [else #f]))

(define debug? #f)
(define steps : (HashTable Integer (Setof -σ)) (make-hasheq))

(: search : (Setof -ς) → (Option (List -blm -Γ (Option (HashTable -e Base)))))
;; Execute from given frontier
(define (search front)
  (cond
    [(set-empty? front) #f]
    [else
     (define front* (batch-step front))
     (when debug?
       (cond
         [(-ς? front*)
          (printf "Done:~n~a~n~n" (dbg-show front*))]
         [else
          (printf "~a. front: ~a~n" (hash-count steps) (set-count front*))
          (for ([ς* front*])
            (printf "  ~a~n" (dbg-show ς*))
            (⊔! steps (hash-count steps) (-ς-σ ς*)))
          (case (read)
            [(skip) (set! debug? #f)]
            [(done) (error "DONE")]
            [else (void)])
          (printf "~n")]))
     (cond
       [(set? front*) (search front*)]
       [else
        (match-define (-ς (? -blm? blm) Γ _ σ _ M) front*)
        (list blm Γ (get-model M σ Γ))])]))

(: batch-step : (Setof -ς) → (U -ς (Setof -ς)))
(define (batch-step front)
  (define ans
    (for/fold ([next : (U -ς (Setof -ς)) ∅]) ([ς front])
      (cond
        [(-ς? next) next] ; Should use #:break, but TR doesn't like it
        [else
         (match (↦/ς ς)
           [(? -ς? ς*) (on-new-state next ς*)]
           [(? set? ςs)
            (for/fold ([next : (U -ς (Setof -ς)) next]) ([ς* ςs])
              (if (-ς? next) next (on-new-state next ς*)))])])))
  #;(when debug?
    (printf "batch-step of (~a) :~n  ~a~nis (~a) ~n  ~a~n~n"
            (set-count front)
            (set-map front dbg-show)
            (if (set? ans) (set-count ans) 1)
            (if (set? ans) (set-map ans dbg-show) (dbg-show ans)))
    (case (read)
      [(skip) (set! debug? #f)]
      [(done) (error "DONE")]
      [else (void)]))
  ans)

(: on-new-state : (Setof -ς) -ς → (U -ς (Setof -ς)))
(define (on-new-state front ς)
  (match ς
    [(-ς (and blm (-blm l+ _ _ _)) _ _ _ _ _)
     (case l+
       [(havoc Λ †) front]
       [else #;(printf "blaming in ~a~n" (dbg-show ς)) ς])]
    ;; Harder to apply heuristic in this setting
    #;[(-ς (? -W?) _ κ _ _ _)
     ]
    [_ (set-add front ς)]))

(: concretize-e : -Γ (HashTable -e Base) -e → -e)
(define (concretize-e Γ mappings e)
  (when debug?
    (printf "concretize:~n")
    (printf "  Γ: ~a~n" (show-Γ Γ))
    (printf "  mappings: ~a~n" mappings)
    (printf "  e: ~a~n" (show-e e)))

  (match-define (-Γ _ φs) Γ)

  (let go ([e e])
    (cond
      [(hash-ref mappings e #f) => -b]
      [else
       (match e
         [(-λ xs e*) (-λ xs (go e*))]
         [(-case-λ clauses)
          (-case-λ (for/list : (Listof (Pairof -formals -e)) ([clause clauses])
                     (match-define (cons xs e*) clause)
                     (cons xs (go e*))))]
         [(and v (-• ℓ))
          (cond
            [(concretized? Γ v) => go]
            [else (blind-guess Γ ℓ)])]
         [(-@ f xs loc)
          (define xs* (map go xs))
          (define (maybe-inline [ef : -e])
            (match ef
              [(-λ (? list? formals) bod)
               (cond
                 [(or (andmap arg-inlinable? xs*)
                      (for/and : Boolean ([x formals]) (<= (count-xs bod x) 1)))
                  (go (e/list (map -x formals) xs* bod))]
                 [else ; default to `let`
                  (-let-values
                   (for/list : (Listof (Pairof (Listof Symbol) -e)) ([x formals] [ex xs*])
                     (cons (list x) ex))
                   (go bod)
                   'havoc)])]
              [_ (-@ (go ef) xs* loc)]))

          (define (cases [f : -•] [x : -e]) : -e
            (define k→v
              (hash->list
               (for/fold ([acc : (HashTable -v -e) (hash)]) ([(k v) mappings])
                 (match k
                   [(-@ (≡ f) (list ek) _)
                    (define k
                      (cond
                        [(-v? ek) ek]
                        [(hash-ref mappings ek #f) => -b]
                        [else (error 'cases "unexpected ~a" (show-e ek))]))
                    (hash-set acc k (-b v))]
                   [_ acc]))))
            (match k→v
              ['() (-b 0)]
              [(cons (cons k₀ v₀) kvs)
               (foldr
                (λ ([p : (Pairof -v -e)] [acc : -e])
                  (-if (-@ 'equal? (list x (car p)) -Λ) (cdr p) acc))
                v₀
                kvs)]))

          (match f
            [(? -•? v)
             (cond [(concretized? Γ v) => maybe-inline]
                   [(equal? '✓ (Γ⊢e Γ (-?@ 'δ-case? v))) (cases v (car xs*))]
                   [else (-begin/simp xs*)])]
            [_ (maybe-inline f)])]
         [(-if e₀ e₁ e₂)
          (case (Γ⊢e Γ e₀)
            [(✓) (go e₁)]
            [(X) (go e₂)]
            [else (-if (go e₀) (go e₁) (go e₂))])]
         [(-wcm k v b) (-wcm (go k) (go v) (go b))]
         [(-begin es) (-begin (map go es))]
         [(-begin0 e₀ es) (-begin0 (go e₀) (map go es))]
         [(-let-values bnds bod ctx)
          (-let-values
           (for/list : (Listof (Pairof (Listof Symbol) -e)) ([bnd bnds])
             (match-define (cons xs ex) bnd)
             (cons xs (go ex)))
           (go bod)
           ctx)]
         [(-letrec-values bnds bod ctx)
          (-letrec-values
           (for/list : (Listof (Pairof (Listof Symbol) -e)) ([bnd bnds])
             (match-define (cons xs ex) bnd)
             (cons xs (go ex)))
           (go bod)
           ctx)]
         [(-set! x e*) (-set! x (go e*))]
         [(-μ/c x c) (-μ/c x (go c))]
         [(-->i doms rst rng pos)
          (-->i
           (for/list : (Listof (Pairof Symbol -e)) ([dom doms])
             (match-define (cons x c) dom)
             (cons x (go c)))
           (match rst
             [(cons x* c*) (cons x* (go c*))]
             [#f #f])
           (go rng)
           pos)]
         [(-struct/c si cs pos) (-struct/c si (map go cs) pos)]
         [e e])])))

;; See if it's ok to inline the application
(define (arg-inlinable? [e : -e])
  (or (-x? e) (-ref? e) (-prim? e)))

(: blind-guess : -Γ Natural → -e)
;; Instantiate the value at given opaque label such that it doesn't contradict path condition
(define (blind-guess -Γ ℓ)
  (define v (-• ℓ))
  #;(error "TODO")
  (-b (string->symbol (format "TODO-~a" ℓ))))

(define (dbg-show [ς : -ς]) : (Listof Sexp)
  (match-define (-ς E Γ κ _ _ _) ς)
  `((E: ,@(show-E E))
    (Γ: ,@(show-Γ Γ))
    (κ: ,@(show-κ κ))))
