#lang typed/racket/base

;; This module implements the simplification of symbolic values
;; This is strictly not needed, but it simplifies/optimizes lots

(provide (all-defined-out))

(require (for-syntax racket/base
                     racket/syntax
                     syntax/parse
                     racket/contract
                     racket/match
                     racket/list
                     racket/function
                     (only-in "../utils/main.rkt" n-sub mk-cond sexp-and))
         racket/match
         (only-in racket/function curry)
         racket/set
         racket/bool
         racket/math
         racket/flonum
         racket/extflonum
         racket/string
         racket/vector
         racket/list
         "../utils/main.rkt"
         "../ast/main.rkt"
         "definition.rkt")

(: -@/simp : -e -e * → -e)
;; Smart constructor for application
(define (-@/simp f . xs)

  (: access-same-value? : -𝒾 (Listof -e) → (Option -e))
  ;; If given expression list of the form like `(car e); (cdr e)`, return `e`.
  ;; Otherwise just `#f`
  (define (access-same-value? 𝒾 es)
    (define n (get-struct-arity 𝒾))
    (match es
      [(cons (-@ (-st-ac 𝒾₀ 0) (list e₀) _) es*)
       (and (equal? 𝒾 𝒾₀)
            (for/and : Boolean ([i (in-range 1 n)] [ei es*])
              (match ei
                [(-@ (-st-ac 𝒾ⱼ j) (list eⱼ) _)
                 (and (equal? 𝒾 𝒾ⱼ) (= i j) (equal? e₀ eⱼ))]
                [_ #f]))
            e₀)]
      [_ #f]))

  (define (default-case)
    (-@ (assert f) (cast xs (Listof -e)) +ℓ₀))

  (match f
    ['any/c -tt]
    ['none/c -ff]
    ['void (-b (void))]
    ['values
     (match xs
       [(list x) x]
       [_ (default-case)])]

    ; vector-length
    ['vector-length
     (match xs
       [(list (-@ 'vector xs _)) (-b (length xs))]
       [_ (default-case)])]

    ; (not³ e) = (not e) 
    ['not
     (match xs
       [(list (-@ 'not (and e* (-@ 'not _ _)) _)) e*]
       [(list (-@ 'not (-b x) _)) (-b (not (not x)))]
       [(list (-b x)) (-b (not x))]
       [(list (-@ '<  (list x y) _)) (-@ '<= (list y x) +ℓ₀)]
       [(list (-@ '<= (list x y) _)) (-@ '<  (list y x) +ℓ₀)]
       [(list (-@ '>  (list x y) _)) (-@ '<= (list x y) +ℓ₀)]
       [(list (-@ '>= (list x y) _)) (-@ '<  (list x y) +ℓ₀)]
       [_ (default-case)])]
    ['not/c
     (match xs
       [(list (-@ 'not/c (list (and e* (-@ 'not/c _ _))) _)) e*]
       [_ (default-case)])]
    [(-@ 'not/c (list f) _)
     (match xs
       [(list x) (-@/simp 'not (-@/simp f x))]
       [_ (default-case)])]

    ; TODO: handle `equal?` generally
    [(? op-≡?)
     (match xs
       [(list (-b b₁) (-b b₂)) (if (equal? b₁ b₂) -tt -ff)]
       [(list x x) -tt]
       [_ (default-case)])]

    ['defined?
      (match xs
        [(list (? -v?)) -tt]
        [_ (default-case)])]

    ['immutable?
     (match xs
       [(list (-@ 'vector _ _)) -ff]
       [_ (default-case)])]

    ['positive?
     (-@/simp '< (-b 0) (car xs))]
    ['negative?
     (-@/simp '< (car xs) (-b 0))]
    ['>
     (-@/simp '< (second xs) (first xs))]
    ['>=
     (-@/simp '<= (second xs) (first xs))]

    ; (car (cons e _)) = e
    [(-st-ac s i)
     (match xs
       [(list (-@ (-st-mk s) es _)) (list-ref es i)]
       [_ (default-case)])]
    [(-st-ac 𝒾 i)
     (match-define (list x) xs)
     (-@ f (list (assert x)) +ℓ₀)]

    ; (cons (car e) (cdr e)) = e
    [(-st-mk s) (or (access-same-value? s xs) (-@ f xs +ℓ₀))]

    ; General case
    [_ (default-case)]))

(: -?@ : -s -s * → -s)
(define (-?@ f . xs)
  (cond
    [(and f (andmap (inst values -s) xs))
     (apply -@/simp f (cast xs (Listof -e)))]
    [else #f]))

;; convenient syntax
(define-match-expander -not
  (syntax-rules () [(_ e) (-@ 'not (list e) _)])
  (syntax-rules () [(_ e) (and e (-@ 'not (list e) +ℓ₀))]))
(define-match-expander -not/c
  (syntax-rules () [(_ p) (-λ (list x) (-@ 'not (list (-@ p (list (-x x)) _)) _))])
  (syntax-rules () [(_ p)
                    (case p
                      [(negative?) (-≥/c 0)]
                      [(positive?) (-≤/c 0)]
                      [else
                       (-λ '(𝒙) (-@ 'not (list (-@ p (list (-x '𝒙)) +ℓ₀)) +ℓ₀))])]))
(define-match-expander -</c
  (syntax-rules () [(_ c) (-λ (list x) (-@ '< (list (-x x) (-b c)) _))])
  (syntax-rules () [(_ c) (-λ '(𝒙) (-@ '< (list (-x '𝒙) (-b c)) +ℓ₀))]))
(define-match-expander -≤/c
  (syntax-rules () [(_ c) (-λ (list x) (-@ '<= (list (-x x) (-b c)) _))])
  (syntax-rules () [(_ c) (-λ '(𝒙) (-@ '<= (list (-x '𝒙) (-b c)) +ℓ₀))]))
(define-match-expander ->/c
  (syntax-rules () [(_ c) (-λ (list x) (-@ '< (list (-b c) (-x x)) _))])
  (syntax-rules () [(_ c) (-λ '(𝒙) (-@ '< (list (-b c) (-x '𝒙)) +ℓ₀))]))
(define-match-expander -≥/c
  (syntax-rules () [(_ c) (-λ (list x) (-@ '<= (list (-b c) (-x x)) _))])
  (syntax-rules () [(_ c) (-λ '(𝒙) (-@ '<= (list (-b c) (-x '𝒙)) +ℓ₀))]))
(define-match-expander -≡/c
  (syntax-rules () [(_ v) (-λ (list x) (-@ (? op-≡?) (or (list (-x x) v)
                                                         (list v (-x x))) _))])
  (syntax-rules () [(_ v) (-λ '(𝒙) (-@ 'equal? (list (-x '𝒙) v) +ℓ₀))]))
(define-match-expander -=/c
  (syntax-rules () [(_ c) (-≡/c (-b c))])
  (syntax-rules () [(_ c) (-≡/c (-b c))]))
(define-match-expander -≢/c
  (syntax-rules () [(_ v) (-λ (list x) (-@ 'not (list (-@ (? op-≡?)
                                                          (or (list (-x x) v)
                                                              (list v (-x x)))
                                                          _))
                                           _))])
  (syntax-rules () [(_ v) (-λ '(𝒙) (-@ 'not (list (-@ 'equal? (list (-x '𝒙) v) +ℓ₀)) +ℓ₀))]))
(define-match-expander -≠/c
  (syntax-rules () [(_ c) (-≢/c (-b c))])
  (syntax-rules () [(_ c) (-≢/c (-b c))]))

(define op-≡? (match-λ? '= 'equal? 'eq? 'char=? 'string=?))

(: -struct/c-split : -s -𝒾 → (Listof -s))
(define (-struct/c-split c 𝒾)
  (with-debugging/off
    ((ans)
     (define n (get-struct-arity 𝒾))
     (match c
       [(-struct/c _ cs _) cs]
       [_
        (for/list : (Listof -s) ([i n])
          (-?@ (-st/c-ac 𝒾 i) c))
        #;(make-list n #f)]))
    (printf "struct/c-split: ~a -> ~a~n" (show-s c) (map show-s ans))))

(: -struct-split : -s -𝒾 → (Listof -s))
(define (-struct-split e 𝒾)
  (match e
    [(-@ (-st-mk (== 𝒾)) es _)
     (for/list ([(e i) (in-indexed es)])
       (if (struct-mutable? 𝒾 (assert i index?)) #f e))]
    [_ (for/list : (Listof -s) ([i (get-struct-arity 𝒾)])
         (-?@ (-st-ac 𝒾 i) e))]))

(: -ar-split : -s → (Values -s -s))
(define (-ar-split s)
  (match s
    [(-ar c e) (values c e)]
    [(? values e) (values (-@ (-ar-ctc) (list e) +ℓ₀) (-@ (-ar-fun) (list e) +ℓ₀))]
    [#f (values #f #f)]))

(: -->-split : -s (U Index arity-at-least) → (Values (-maybe-var -s) -s))
(define (-->-split s shape)
  (define n
    (match shape
      [(arity-at-least n) (assert n index?)]
      [(? index? n) n]))
  (define var? (arity-at-least? shape))
  (match s
    [(--> cs d _) (values cs d)]
    [(? values e)
     (define inits : (Listof -e)
       (for/list ([i : Index n])
         (-@ (-->-ac-dom i) (list e) +ℓ₀)))
     (values (cond [var? (-var inits (-@ (-->-ac-rst) (list e) +ℓ₀))]
                   [else inits])
             (-@ (-->-ac-rng) (list e) +ℓ₀))]
    [#f
     (values (if var? (-var (make-list n #f) #f) (make-list n #f))
             #f)]))

(: -->i-split : -s Index → (Values (Listof -s) -s))
(define (-->i-split s n)
  (match s
    [(-->i cs mk-d _) (values cs mk-d)]
    [(? values e)
     (values (for/list : (Listof -s) ([i n])
               (-@ (-->i-ac-dom i) (list e) +ℓ₀))
             (-@ (-->i-ac-rng) (list e) +ℓ₀))]
    [#f (values (make-list n #f) #f)])) 

(define (-?ar [c : -s] [v : -s]) : -s
  (and c v (-ar c v)))

(define (-?list [es : (Listof -s)]) : -s
  (foldr (curry -?@ -cons) -null es))

(define (-?unlist [e : -s] [n : Natural]) : (Listof -s)
  (let go ([e : -s e] [n : Integer n])
    (cond [(> n 0) (cons (-?@ -car e) (go (-?@ -cdr e) (- n 1)))]
          [else '()])))

(: -app-split : -s -o Integer → (Listof -s))
(define (-app-split e o n)
  (match e
    [(-@ (== o) es _) es]
    [_ (make-list n #f)]))

(define (-?μ/c [x : Symbol] [e : -s]) (and e (-μ/c x e)))

(: -?struct/c : -𝒾 (Listof -s) → (Option -struct/c))
(define (-?struct/c 𝒾 fields)
  (and (andmap (inst values -s) fields)
       (-struct/c 𝒾 (cast fields (Listof -e)) +ℓ₀)))

(: -?-> : (-maybe-var -s) -s ℓ -> (Option -->))
(define (-?-> cs d ℓ)
  (define cs* (check-ss cs))
  (and d cs* (--> cs* d ℓ)))

(: -?->i : (Listof -s) (Option -λ) ℓ -> (Option -->i))
(define (-?->i cs mk-d ℓ)
  (define cs* (check-ss cs))
  (and mk-d cs* (-->i cs* mk-d ℓ)))

(: split-values : -s Natural → (Listof -s))
;; Split a pure expression `(values e ...)` into `(e ...)`
(define (split-values e n)
  (match e
    [(-@ 'values es _)
     (cond [(= n (length es)) es]
           [else (error 'split-values "cannot split ~a values into ~a" (length es) n)])]
    [(? -e?)
     (cond [(= 1 n) (list e)]
           [else #|hack|#
            (for/list ([i : Natural n])
              (-?@ (format-symbol "values@~a" i) e))])]
    [_ (make-list n #f)]))

(: bind-args : -formals (Listof -s) → (Values (Listof Symbol) (Listof -s)))
;; Bind arguments to formals at `?e` level.
;; Return 2 lists for parameters and arguments of equal lengths.
(define (bind-args xs es)
  (match xs
    [(? list? xs) (values xs es)]
    [(-var xs x)
     (define-values (es-init es-rest) (split-at es (length xs)))
     (values `(,@xs ,x) `(,@es-init ,(-?list es-rest)))]))

(: check-ss : (case->
               [(Listof -s) → (Option (Listof -e))]
               [(-var -s) → (Option (-var -e))]
               [(-maybe-var -s) → (Option (-maybe-var -e))]))
(define (check-ss ss)

  (: go : (Listof -s) → (Option (Listof -e)))
  (define (go ss)
    (match ss
      ['() '()]
      [(cons s ss*)
       (and s
            (let ([es (go ss*)])
              (and es (cons s es))))]))

  (match ss
    [(? list? ss) (go ss)]
    [(-var ss s)
     (define ss* (go ss))
     (and ss* s (-var ss* s))]))

(: keep-if-const : -s ℓ -⟪ℋ⟫ → (Option -α.e))
;; Keep expression if it evaluates to a fixed value
(define (keep-if-const s ℓ ⟪ℋ⟫)
  ;; TODO: update to work with mutable states
  (and s (set-empty? (fv s)) (-α.e s ℓ ⟪ℋ⟫)))

(module+ test
  (require typed/rackunit)
  (check-equal? (-?@ 'not (-?@ 'not (-?@ 'not (-x 'x)))) (-?@ 'not (-x 'x)))
  (check-equal? (-?@ -car (-?@ -cons (-b 1) (-x 'x))) (-b 1))
  (check-equal? (-?@ '+ (-x 'x) (-b 0)) (-x 'x))
  (check-equal? (-?@ '+ (-b 0) (-x 'x)) (-x 'x))
  (check-equal? (-?@ '* (-?@ '* (-x 'x) (-x 'y)) (-x 'z))
                (-?@ '* (-x 'x) (-?@ '* (-x 'y) (-x 'z))))
  (let ([e (assert (-?@ '+ (-x 'x) (-x 'y)))])
    (check-equal? (-?@ -cons (-?@ -car e) (-?@ -cdr e)) e)
    (check-equal? (-?@ -cons (-?@ -cdr e) (-?@ -car e))
                  (-@ -cons (list (-@ -cdr (list e) +ℓ₀) (-@ -car (list e) +ℓ₀)) +ℓ₀))))
