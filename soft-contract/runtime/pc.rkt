#lang typed/racket/base

(require typed/racket/unit
         racket/match
         racket/set
         racket/list
         (except-in racket/function normalize-arity arity-includes?)
         set-extras
         "../utils/main.rkt"
         "../ast/main.rkt"
         "signatures.rkt")

(provide pc@)

(define-unit pc@
  (import env^)
  (export pc^)

  (define ⊤Γ ∅)

  (: t-contains? : -t -t → Boolean)
  (define (t-contains? t t*)
    (let go ([t : -t t])
      (match t
        [t #:when (equal? t t*) #t]
        [(-t.@ _ ts) (ormap go ts)]
        [_ #f])))

  (: t-contains-any? : -t (℘ -t) → Boolean)
  (define (t-contains-any? t ts)
    (let go ([t : -t t])
      (match t
        [t #:when (∋ ts t) #t]
        [(-t.@ _ ts) (ormap go ts)]
        [_ #f])))

  (: bin-o->h : -special-bin-o → Base → -h)
  (define (bin-o->h o)
    (case o
      [(>) ->/c]
      [(<) -</c]
      [(>=) -≥/c]
      [(<=) -≤/c]
      [(= equal? eqv? eq?) -≡/c]
      [(≢) -≢/c]))

  (: flip-bin-o : -special-bin-o → -special-bin-o)
  ;; Returns o* such that (o l r) ↔ (o* r l)
  (define (flip-bin-o o)
    (case o
      [(<) '>]
      [(>) '<]
      [(>=) '<=]
      [(<=) '>=]
      [else o]))

  (: neg-bin-o : -special-bin-o → -special-bin-o)
  ;; Returns o* such that (o l r) ↔ (not (o* l r))
  (define (neg-bin-o o)
    (case o
      [(<) '>=]
      [(>) '<=]
      [(>=) '<]
      [(<=) '>]
      [(= equal? eqv? eq?) '≢]
      [(≢) 'equal?]))


  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
  ;;;;;
  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (: fv-as : (HashTable Symbol -t) → (℘ Symbol))
  (define (fv-as as)
    (for/unioneq : (℘ Symbol) ([(x t) (in-hash as)])
                 (set-add (fvₜ t) x)))

  (: fvₜ : -?t → (℘ Symbol))
  (define (fvₜ t)
    (match t
      [(-t.@ h ts) (apply set-union ∅eq (map fvₜ ts))]
      [(? -e? e) (fv e)]
      [#f ∅eq]))

  (define (?t↓ [?t : -?t] [xs : (℘ Symbol)]) (and ?t (t↓ ?t xs)))

  (: t↓ : -t (℘ Symbol) → -?t)
  (define (t↓ t xs)
    (and (not (set-empty? (∩ (fvₜ t) xs))) #;(⊆ (fv e) xs) t))

  (: Γ↓ : -Γ (℘ Symbol) → -Γ)
  (define (Γ↓ ts xs)
    (for*/set: : -Γ ([t ts]
                     [t* (in-value (t↓ t xs))] #:when t*)
      t*))

  (: predicates-of : -Γ -?t → (℘ -h))
  ;; Extract predicates that hold on given symbol
  (define (predicates-of Γ t)
    (cond
      [t
       ;; tmp hack for integer precision
       ;; TODO: these hacks will be obsolete when the `def-prim` DSL is generalized
       (define ps : (℘ -h)
         (match t
           [(-t.@ '+ (or (list t* (-b (and (? real?) (? positive?))))
                         (list (-b (and (? real?) (? positive?))) t*)))
            #:when (and t* (∋ Γ (-t.@ '<= (list -zero t*))))
            {set (->/c 0)}]
           [(-t.@ '* (list t t))
            {set (-≥/c 0)}]
           [(-t.@ '- (list t₁ t₂))
            (cond [(or (∋ Γ (-t.@ '<= (list t₂ t₁)))
                       (∋ Γ (-t.@ '>= (list t₁ t₂))))
                   {set (-≥/c 0)}]
                  [(or (∋ Γ (-t.@ '< (list t₂ t₁)))
                       (∋ Γ (-t.@ '> (list t₁ t₂))))
                   {set (->/c 0)}]
                  [else ∅])]
           [_ ∅]))
       (for/fold ([ps : (℘ -h) ps]) ([φ (in-set Γ)])
         (match φ
           ;; unary
           [(-t.@ 'negative? (list (== t))) (set-add ps (-</c 0))]
           [(-t.@ 'positive? (list (== t))) (set-add ps (->/c 0))]
           ;; binary
           [(-t.@ (? -special-bin-o? o) (list (== t) (-b b)))
            (set-add ps ((bin-o->h o) b))]
           [(-t.@ (? -special-bin-o? o) (list (-b b) (== t)))
            (set-add ps ((bin-o->h (flip-bin-o o)) b))]
           ;; negate unary
           [(-t.@ 'not (list (-t.@ (? -o? o) (list (== t)))))
            (set-add ps (-not/c o))]
           ;; negate binary
           [(-t.@ 'not (list (-t.@ (? -special-bin-o? o) (list (== t) (-b b)))))
            (set-add ps ((bin-o->h (neg-bin-o o)) b))]
           [(-t.@ 'not (list (-t.@ (? -special-bin-o? o) (list (-b b) (== t)))))
            (set-add ps ((bin-o->h (neg-bin-o (flip-bin-o o))) b))]
           [(-t.@ h (list (== t))) (set-add ps h)]
           [_ ps]))]
      [else ∅]))

  (: complement? : -t -t → Boolean)
  (define complement?
    (match-lambda**
     [(φ (-t.@ 'not (list φ))) #t]
     [((-t.@ 'not (list φ)) φ) #t]
     [((-t.@ '<  (list t₁ t₂))
       (-t.@ '<= (list t₂ t₁))) #t]
     [((-t.@ '<= (list t₂ t₁))
       (-t.@ '<  (list t₁ t₂))) #t]
     [(_ _) #f]))


  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
  ;;;;; Simplification
  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (: ?t@ : (Option -h) -?t * → -?t)
  (define (?t@ f . xs)

    (: t@ : -h -t * → -t)
    ;; Smart constructor for term application
    (define (t@ f . xs)

      (: access-same-value? : -𝒾 (Listof -t) → (Option -t))
      ;; If given term list of the form `(car t); (cdr t)`, return `t`.
      ;; Otherwise just `#f`
      (define (access-same-value? 𝒾 ts)
        (define n (get-struct-arity 𝒾))
        (match ts
          [(cons (-t.@ (-st-ac 𝒾₀ 0) (list t₀)) ts*)
           (and (equal? 𝒾 𝒾₀)
                (for/and : Boolean ([i (in-range 1 n)] [tᵢ ts*])
                  (match tᵢ
                    [(-t.@ (-st-ac 𝒾ⱼ j) (list tⱼ))
                     (and (equal? 𝒾 𝒾ⱼ) (= i j) (equal? t₀ tⱼ))]
                    [_ #f]))
                t₀)]
          [_ #:when (equal? n 0) (-t.@ (-st-mk 𝒾) '())]
          [_ #f]))

      (define (default-case) (-t.@ f xs))

      (match f
        ['any/c -tt]
        ['none/c -ff]
        ['void -void]
        ['values
         (match xs
           [(list x) x]
           [_ (default-case)])]

        ; vector-length
        ['vector-length
         (match xs
           [(list (-t.@ 'vector xs)) (-b (length xs))]
           [_ (default-case)])]

        ; (not³ e) = (not e) 
        ['not
         (match xs
           [(list (-t.@ 'not (list (and t* (-t.@ 'not _))))) t*]
           [(list (-t.@ 'not (list (-b x)))) (-b (not (not x)))]
           [(list (-b x)) (-b (not x))]
           [(list (-t.@ '<  (list x y))) (-t.@ '<= (list y x))]
           [(list (-t.@ '<= (list x y))) (-t.@ '<  (list y x))]
           [(list (-t.@ '>  (list x y))) (-t.@ '<= (list x y))]
           [(list (-t.@ '>= (list x y))) (-t.@ '<  (list x y))]
           [_ (default-case)])]
        ['not/c
         (match xs
           [(list (-t.@ 'not/c (list (and t* (-t.@ 'not/c _))))) t*]
           [_ (default-case)])]

        ; TODO: handle `equal?` generally
        [(? op-≡?)
         (match xs
           [(list (-b b₁) (-b b₂)) (if (equal? b₁ b₂) -tt -ff)]
           [(or (list t (-b #f)) (list (-b #f) t)) #:when t
            (-t.@ 'not (list t))]
           [(list x x) -tt]
           [_ (default-case)])]

        ['defined?
          (match xs
            [(list (? -v?)) -tt]
            [_ (default-case)])]

        ['immutable?
         (match xs
           [(list (-t.@ 'vector _)) -ff] ; for now
           [_ (default-case)])]

        ['positive?
         (t@ '< (-b 0) (car xs))]
        ['negative?
         (t@ '< (car xs) (-b 0))]
        ['>
         (t@ '< (second xs) (first xs))]
        ['>=
         (t@ '<= (second xs) (first xs))]

        ; (car (cons e _)) = e
        [(-st-ac 𝒾 i)
         (match xs
           [(list (-t.@ (-st-mk (== 𝒾)) ts)) (list-ref ts i)]
           [_ (default-case)])]

        ; (cons (car e) (cdr e)) = e
        [(-st-mk s) (or (access-same-value? s xs) (default-case))]

        ; st-pred
        [(-st-p 𝒾)
         (match xs
           [(list (? -b?)) -ff]
           [_ (default-case)])]

        [(or 'null? 'integer? 'real? 'number? 'string? 'symbol?) ; TODO fix
         (match xs
           [(list (-t.@ (-st-mk _) _)) -ff]
           [_ (default-case)])]
        
        ; HACK
        ['+
         (match xs
           [(list b (-t.@ '- (list t b))) t]
           [_ (default-case)])]

        ; General case
        [_ (default-case)]))

    (and f (andmap -t? xs) (apply t@ f xs)))

  (define op-≡? (match-λ? '= 'equal? 'eq? 'char=? 'string=?))

  (: -struct/c-split : -?t -𝒾 → (Listof -?t))
  (define (-struct/c-split t 𝒾)
    (with-debugging/off
      ((ans)
       (define n (get-struct-arity 𝒾))
       (match t
         [(-t.@ (-st/c.mk (== 𝒾)) cs) cs]
         [(? values t)
          (for/list : (Listof -t) ([i n])
            (-t.@ (-st/c.ac 𝒾 i) (list t)))]
         [#f (make-list n #f)]))
      (printf "struct/c-split: ~a -> ~a~n" (show-t c) (map show-t ans))))

  (: -struct-split : -?t -𝒾 → (Listof -?t))
  (define (-struct-split t 𝒾)
    (match t
      [(-t.@ (-st-mk (== 𝒾)) ts) ts]
      [(? values t)
       (for/list : (Listof -t) ([i (get-struct-arity 𝒾)])
         (-t.@ (-st-ac 𝒾 i) (list t)))]
      [#f (make-list (get-struct-arity 𝒾) #f)]))

  (: -ar-split : -?t → (Values -?t -?t))
  (define (-ar-split t)
    (match t
      [(-t.@ (-ar.mk) (list c e)) (values c e)]
      [(? values t) (values (-t.@ (-ar.ctc) (list t))
                            (-t.@ (-ar.fun) (list t)))]
      [#f (values #f #f)]))

  (: -->-split : -?t (U Index arity-at-least) → (Values (-maybe-var -?t) -?t))
  (define (-->-split t shape)
    (define n
      (match shape
        [(arity-at-least n) (assert n index?)]
        [(? index? n) n]))
    (define var? (arity-at-least? shape))
    (match t
      [(-t.@ (-->.mk) (list cs ... d)) (values (cast cs (Listof -t)) d)]
      [(-t.@ (-->*.mk) (list cs ... cᵣ d)) (values (-var (cast cs (Listof -t)) cᵣ) d)]
      [(? values t)
       (define inits : (Listof -t)
         (for/list ([i : Index n])
           (-t.@ (-->.dom i) (list t))))
       (values (if var? (-var inits (-t.@ (-->.rst) (list t))) inits)
               (-t.@ (-->.rng) (list t)))]
      [#f
       (values (if var? (-var (make-list n #f) #f) (make-list n #f))
               #f)]))


  (: -->i-split : -?t Index → (Values (Listof -?t) -?t))
  (define (-->i-split t n)
    (match t
      [(-t.@ (-->i.mk) (list cs ... mk-d)) (values (cast cs (Listof -t)) mk-d)]
      [(? values t)
       (values (for/list : (Listof -t) ([i n])
                 (-t.@ (-->i.dom i) (list t)))
               (-t.@ (-->i.rng) (list t)))]
      [#f (values (make-list n #f) #f)])) 

  (define (-?list [ts : (Listof -?t)]) : -?t
    (foldr (curry ?t@ -cons) -null ts))

  (define (-?unlist [t : -?t] [n : Natural]) : (Listof -?t)
    (let go ([t : -?t t] [n : Integer n])
      (cond [(> n 0) (cons (?t@ -car t) (go (?t@ -cdr t) (- n 1)))]
            [else '()])))

  (: -app-split : -h -?t Integer → (Listof -?t))
  (define (-app-split h t n)
    (match t
      [(-t.@ (== h) ts) ts]
      [_ (make-list n #f)]))

  (: -?-> : (-maybe-var -?t) -?t -> -?t)
  (define (-?-> cs d)
    (define cs* (check-ts cs))
    (and d cs* (-t.@ (-->.mk)
                     (match cs*
                       [(-var cs₀ cᵣ) `(,@cs₀ ,cᵣ ,d)]
                       [(? list? cs*) `(,@cs*     ,d)]))))



  (: -?->i : (Listof -?t) (Option -λ) → -?t)
  (define (-?->i cs mk-d)
    (and mk-d
         (let ([cs* (check-ts cs)])
           (and cs* (-t.@ (-->i.mk) `(,@cs* ,mk-d))))))

  (: split-values : -?t Natural → (Listof -?t))
  ;; Split a pure term `(values t ...)` into `(t ...)`
  (define (split-values t n)
    (match t
      [(-t.@ 'values ts)
       (cond [(= n (length ts)) ts]
             [else (error 'split-values "cannot split ~a values into ~a" (length ts) n)])]
      [(? values)
       (cond [(= 1 n) (list t)]
             [else
              (for/list ([i n])
                (-t.@ (-values.ac (assert i index?)) (list t)))])]
      [_ (make-list n #f)]))

  (: check-ts (case->
               [(Listof -?t) → (Option (Listof -t))]
               [(-var -?t) → (Option (-var -t))]
               [(-maybe-var -?t) → (Option (-maybe-var -t))]))
  (define (check-ts ts)

    (: go : (Listof -?t) → (Option (Listof -t)))
    (define (go ts)
      (match ts
        ['() '()]
        [(cons t ts*)
         (and t
              (let ([ts** (go ts*)])
                (and ts** (cons t ts**))))]))

    (match ts
      [(? list? ts) (go ts)]
      [(-var ts t)
       (and t
            (let ([ts* (go ts)])
              (and ts* (-var ts* t))))]))
  )
