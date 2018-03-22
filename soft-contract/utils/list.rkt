#lang typed/racket/base

(provide NeListof Assoc unzip-by unzip cartesian)
(require racket/match
         racket/list
         racket/set)

(define-type (NeListof X) (Pairof X (Listof X)))
(define-type (Assoc X Y) (Listof (Pairof X Y)))

(: unzip-by (∀ (A X Y) (A → X) (A → Y) (Listof A) → (Values (Listof X) (Listof Y))))
;; Given a pair of functions, split list into 2
(define (unzip-by f g l)
  (for/lists ([xs : (Listof X)] [ys : (Listof Y)]) ([a : A l])
    (values (f a) (g a))))

(: unzip (∀ (X Y) (Listof (Pairof X Y)) → (Values (Listof X) (Listof Y))))
;; Unzip list of pairs into 2 lists
(define (unzip l)
  (unzip-by (inst car X Y) (inst cdr X Y) l))

(: maybe-map (∀ (X Y) (X → (Option Y)) (Listof X) → (Option (Listof Y))))
(define (maybe-map f xs)
  (match xs
    ['() '()]
    [(cons x xs*)
     (define ?y (f x))
     (and ?y (let ([?ys (maybe-map f xs*)])
               (and ?ys (cons ?y ?ys))))]))

(: init/last (∀ (X) (Listof X) → (Values (Listof X) X)))
(define (init/last l)
  (cond [(pair? l)
         (match-define-values (xs (list x)) (split-at l (sub1 (length l))))
         (values xs x)]
        [else (error 'init/last "empty list")]))

(: cartesian (∀ (X Y)
                (case->
                 [(Listof (Setof X)) → (Listof (Listof X))]
                 [(Listof (Setof X)) (X → Boolean : Y) → (Listof (Listof Y))])))
(define cartesian
  (case-lambda
    [(xs) (apply cartesian-product (map (inst set->list X) xs))]
    [(xs ok?)
     (let go ([xs : (Listof (Setof X)) xs])
       (match xs
         [(cons x xs)
          (define y (for/list : (Listof Y) ([xᵢ (in-set x)] #:when (ok? xᵢ)) xᵢ))
          (cond
            [(null? y) '()]
            [else
             (define ps (go xs))
             (for*/list : (Listof (Listof Y)) ([yⱼ (in-list y)] [pᵢ (in-list ps)])
               (cons yⱼ pᵢ))])]
         [_ '{()}]))]))
