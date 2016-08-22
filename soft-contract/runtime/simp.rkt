#lang typed/racket/base

;; This module implements the simplification of symbolic values
;; This is strictly not needed, but it simplifies/optimizes lots

(provide (all-defined-out))

(require racket/match
         racket/set
         (except-in racket/function arity-includes?)
         (except-in racket/list remove-duplicates)
         "../utils/main.rkt"
         "../ast/main.rkt"
         "definition.rkt")

(: -?@ : -s -s * → -s)
(define (-?@ f . xs)
  (cond
    [(and f (andmap (inst values -s) xs))
     (apply -@/simp f (cast xs (Listof -e)))]
    [else #f]))

;; convenient syntax for negation
(define-match-expander -not
  (syntax-rules () [(_ e) (-@ 'not (list e) _)])
  (syntax-rules () [(_ e) (and e (-@ 'not (list e) +ℓ₀))]))

(: -struct/c-split : -s Integer → (Listof -s))
(define (-struct/c-split c n)
  (with-debugging/off
    ((ans)
     (match c
       [(-struct/c _ cs _) cs]
       [_ (make-list n #f)]))
    (printf "struct/c-split: ~a -> ~a~n" (show-s c) (map show-s ans))))

(: -struct-split : -s -struct-info → (Listof -s))
(define (-struct-split e s)
  (match e
    [(-@ (-st-mk (== s)) es _)
     (define mutables (-struct-info-mutables s))
     (for/list ([(e i) (in-indexed es)])
       (if (∋ mutables i) #f e))]
    [_ (for/list : (Listof -s) ([i : Natural (-struct-info-arity s)])
         (-?@ (-st-ac s i) e))]))

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

(define (-?μ/c [x : -ℓ] [e : -s]) (and e (-μ/c x e)))

(: -?struct/c : -struct-info (Listof -s) → (Option -struct/c))
(define (-?struct/c s fields)
  (and (andmap (inst values -s) fields)
       (-struct/c s (cast fields (Listof -e)) +ℓ₀)))

(: -?-> : (Listof -s) -s -> (Option -->))
(define (-?-> cs d)
  (define cs* (check-ss cs))
  (and d cs* (--> cs* d +ℓ₀)))

(: -?->i : (Listof -s) (Option -λ) -> (Option -->i))
(define (-?->i cs mk-d)
  (define cs* (check-ss cs))
  (and mk-d cs* (-->i cs* mk-d +ℓ₀)))

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
            (define s (-struct-info -𝒾-values n ∅eq))
            (for/list ([i : Natural n])
              (-?@ (-st-ac s i) e))])]
    [_ (make-list n #f)]))

(: bind-args : -formals (Listof -s) → (Values (Listof Var-Name) (Listof -s)))
;; Bind arguments to formals at `?e` level.
;; Return 2 lists for parameters and arguments of equal lengths.
(define (bind-args xs es)
  (match xs
    [(? list? xs) (values xs es)]
    [(-varargs xs x)
     (define-values (es-init es-rest) (split-at es (length xs)))
     (values `(,@xs ,x) `(,@es-init ,(-?list es-rest)))]))

(: check-ss : (Listof -s) → (Option (Listof -e)))
(define (check-ss ss)
  (let go ([ss : (Listof -s) ss])
    (match ss
      ['() '()]
      [(cons s ss*)
       (and s
            (let ([es (go ss*)])
              (and es (cons s es))))])))

(: keep-if-const : -s → -s)
;; Keep expression if it evaluates to a fixed value
(define (keep-if-const s)
  ;; TODO: update to work with mutable states
  (and s (set-empty? (fv s)) s))

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
