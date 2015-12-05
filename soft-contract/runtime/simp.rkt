#lang typed/racket/base

(provide -?@ -not -struct/c-split -struct-split -app-split -?struct/c -?->i split-values)

(require
 racket/match racket/bool racket/list racket/math racket/flonum racket/extflonum racket/string
 "../utils/untyped-macros.rkt" "../utils/set.rkt" "../ast/definition.rkt" "path-inv.rkt"
 (for-syntax
  racket/base racket/contract racket/match racket/list racket/function
  "../utils/set.rkt" "../utils/sexp-stx.rkt" "../utils/pretty.rkt"
  (prefix-in prims: "../primitives/declarations.rkt") "../primitives/utils.rkt"))

;; Helper syntax definition(s) for `-?@`
(begin-for-syntax

  (define/contract (general-primitive-clauses f xs)
    (identifier? identifier? . -> . (listof syntax?))

    (define default-case (datum->syntax f '(default-case)))

    (define/contract (go dec)
      (any/c . -> . (listof syntax?))
      (match dec
        [`(#:pred ,(? symbol? s))
         (go `(,s (any/c . -> . boolean?) #:other-errors))]
        [`(#:pred ,(? symbol? s) (,(? prims:ctc? cs) ...))
         (go `(,s (,@cs . -> . boolean?) #:other-errors))]
        [`(#:batch (,(? symbol? ss) ...) ,(? prims:arr? c) ,_ ...)
         (append-map (λ (s) (go `(,s ,c #:other-errors))) ss)]
        [`(,(and (? symbol?) (not (? ignore-for-now?)) o) (,cs ... . -> . ,d) ,_ ...)

         (cond
           [(or (base? o) (and (andmap base? cs) (base? d)))
            
            (define/contract b-syms (listof symbol?)
              (build-list (length cs) (λ (i) (string->symbol (format "x~a" (n-sub i))))))
            (define/contract b-ids (listof identifier?) (map (curry datum->syntax f) b-syms))
            (define b-pats (for/list ([b-id b-ids]) #`(-b #,b-id)))
            (define b-conds (datum->syntax f (sexp-and (map mk-cond b-syms cs))))

            (list
             #`[(#,o)
                (match #,xs
                  [(list #,@b-pats) #:when #,b-conds (-b (#,o #,@b-ids))]
                  #,@(cond
                       [(hash-ref prims:left-ids o #f) =>
                        (λ (lid) (list #`[(list (-b #,lid) e) e]))]
                       [else '()])
                  #,@(cond
                       [(hash-ref prims:right-ids o #f) =>
                        (λ (rid) (list #`[(list e (-b #,rid)) e]))]
                       [else '()])
                  #,@(cond
                       [(∋ prims:assocs o)
                        (list #`[(list (-@ '#,o (list e₁ e₂) _) e₃)
                                 (-?@ '#,o e₁ (-?@ '#,o e₂ e₃))])]
                       [else '()])
                  [_ #,default-case])])]
           [else '()])]
        [_ '()]))
    
    (define ans (append-map go prims:prims))
    ;(printf "~a~n" (pretty (map syntax->datum ans)))
    ans))

(: -?@ : -?e -?e * → -?e)
;; Smart constructor for application
(define (-?@ f . xs)

  (: access-same-value? : -struct-info (Listof -?e) → (Option -e))
  ;; If given expression list of the form like `(car e); (cdr e)`, return `e`.
  ;; Otherwise just `#f`
  (define (access-same-value? info es)
    (define n (-struct-info-arity info))
    (match es
      [(cons (-@ (-st-ac info₀ 0) (list e₀) _) es*)
       (and (equal? info info₀)
            (for/and : Boolean ([i (in-range 1 n)] [ei es*])
              (match ei
                [(-@ (-st-ac infoⱼ j) (list eⱼ) _)
                 (and (equal? info infoⱼ) (= i j) (equal? e₀ eⱼ))]
                [_ #f]))
            e₀)]
      [_ #f]))

  (define (default-case) : -e
    (-@ (assert f) (cast xs (Listof -e)) -Λ))

  (define-syntax (general-primitive-case stx)
    #`(case f
        #,@(general-primitive-clauses #'f #'xs)
        [else (default-case)]))
  
  (cond
    [(and f (andmap (inst values -?e) xs))
     (match f
       ['any/c -tt]
       ['none/c -ff]
       ['void (-b (void))]

       ; vector-length
       ['vector-length
        (match xs
          [(list (-@ 'vector xs _)) (-b (length xs))]
          [_ (default-case)])]

       ; (not³ e) = (not e) 
       ['not
        (match xs
          [(list (-not (and e* (-not _)))) e*]
          [(list (-not (-b x))) (-b (not (not x)))]
          [(list (-b x)) (-b (not x))]
          [_ (default-case)])]
       ['not/c
        (match xs
          [(list (-@ 'not/c (list (and e* (-@ 'not/c _ _))) _)) e*]
          [_ (default-case)])]
       [(-@ 'not/c (list f) _)
        (match xs
          [(list x) (-?@ 'not (-?@ f x))]
          [_ (default-case)])]

       ; TODO: handle `equal?` generally
       ['equal?
        (match xs
          [(list (-b b₁) (-b b₂)) (if (equal? b₁ b₂) -tt -ff)]
          [(list x x) -tt]
          [_ (default-case)])]

       ; (car (cons e _)) = e
       [(-st-ac s i)
        (match xs
          [(list (-@ (-st-mk s) es _)) (list-ref es i)]
          [_ (default-case)])]
       [(-st-ac s i)
        (match-define (list x) xs)
        (cond ; don't build up syntax when reading from mutable states
          [(∋ (-struct-info-mutables s) i) #f]
          [else (-@ f (list (assert x)) -Λ)])]

       ; (cons (car e) (cdr e)) = e
       [(-st-mk s)
        (or (access-same-value? s xs)
            (-@ f (cast xs (Listof -e)) -Λ))]

       ; General case
       [_ (general-primitive-case)])]
    [else #f]))

;; convenient syntax for negation
(define-match-expander -not
  (syntax-rules () [(_ e) (-@ 'not (list e) _)])
  (syntax-rules () [(_ e) (-?@ 'not e)]))

(: -struct/c-split : -?e Integer → (Listof -?e))
(define (-struct/c-split c n)
  (match c
    [(-struct/c _ cs _) cs]
    [_ (make-list n #f)
     #;(define s (-struct-info 'struct/c n ∅)) ; hack
     #;(for/list : (Listof -?e) ([i (in-range n)])
         (-?@ (-st-ac s i) c))]))

(: -struct-split : -?e -struct-info → (Listof -?e))
(define (-struct-split e s)
  (match e
    [(-@ (-st-mk (≡ s)) es _)
     (define mutables (-struct-info-mutables s))
     (for/list ([(e i) (in-indexed es)])
       (if (∋ mutables i) #f e))]
    [_ (for/list : (Listof -?e) ([i (in-range (-struct-info-arity s))])
         (-?@ (-st-ac s i) e))]))

(: -app-split : -?e -o Integer → (Listof -?e))
(define (-app-split e o n)
  (match e
    [(-@ (≡ o) es _) es]
    [_ (make-list n #f)]))

(: -?struct/c : -struct-info (Listof -?e) → (Option -struct/c))
(define (-?struct/c s fields)
  (and (andmap (inst values -?e) fields)
       (-struct/c s (cast fields (Listof -e)) 0)))

(: -?->i : (Listof Symbol) (Listof -?e) -?e -> (Option -->i))
(define (-?->i xs cs d)
  (and d (andmap (inst values -?e) cs)
       (-->i (map (inst cons Symbol -e) xs (cast cs (Listof -e))) d 0)))

(: split-values : -?e Integer → (Listof -?e))
;; Split a pure expression `(values e ...)` into `(e ...)`
(define (split-values e n)
  (match e
    [(-@ 'values es _)
     (cond [(= n (length es)) es]
           [else (error 'split-values "cannot split ~a values into ~a" (length es) n)])]
    [(? -e?)
     (cond [(= 1 n) (list e)]
           [else #|hack|#
            (define s (-struct-info 'values n ∅))
            (for/list ([i (in-range n)])
              (-?@ (-st-ac s i) e))])]
    [_ (make-list n #f)]))

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
                  (-@ -cons (list (-@ -cdr (list e) -Λ) (-@ -car (list e) -Λ)) -Λ))))
