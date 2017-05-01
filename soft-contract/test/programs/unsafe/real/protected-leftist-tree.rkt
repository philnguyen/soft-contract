#lang racket/base

(require racket/match
         racket/function
         #;racket/contract/base)

;; adapted from http://typeocaml.com/2015/03/12/heap-leftist-tree/

(define (leftist-tree-write t out mode)
  (cond [(leftist-tree-empty? t)
         (fprintf out "#<leftist-tree [empty]>")]
        [else
         (fprintf out
                  "#<leftist-tree [count=~a; min=~s]>"
                  (leftist-tree-count t)
                  (leftist-tree-min t))]))

(struct leftist (<=? root)
  #:methods gen:custom-write
  [(define write-proc leftist-tree-write)])

(struct node (rank key left right))

(define tree/c
  (or/c not
        (struct/c node
                  exact-nonnegative-integer?
                  any/c
                  (recursive-contract tree/c)
                  (recursive-contract tree/c))))
(define leftist-tree/c (struct/c leftist (any/c any/c . -> . any/c) tree/c))

(define (leftist-tree <=? xs)
  (leftist-tree-add-all (leftist <=? #f) xs))

(define (leftist-tree? x)
  (leftist? x))

(define (leftist-tree-empty? t)
  (not (leftist-root t)))

(define (leftist-tree-count t)
  (node-count (leftist-root t)))

(define (leftist-tree-add t x)
  (match-define (leftist <=? root) t)
  (leftist <=? (insert root x <=?)))

(define (leftist-tree-add-all t xs)
  (for/fold ([t t]) ([x xs]) (leftist-tree-add t x)))

(define (leftist-tree-min t)
  (match (get-min (leftist-root t))
    [(== *nothing*) (raise
                     (exn:fail:contract
                      "leftist-tree-min: empty tree"
                      (current-continuation-marks)))]
    [x x]))

(define (leftist-tree-remove-min t)
  (match-define (leftist <=? root) t)
  (match (remove-min root <=?)
    [(== *nothing*) (raise
                     (exn:fail:contract
                      "leftist-tree-remove-min: empty tree"
                      (current-continuation-marks)))]
    [n (leftist <=? n)]))

(define (in-leftist-tree t)
  (make-do-sequence
   (λ ()
     (values leftist-tree-min
             leftist-tree-remove-min
             t
             (negate leftist-tree-empty?)
             #f
             #f))))

(define (leftist-tree->list t)
  (for/list ([x (in-leftist-tree t)]) x))

(define (node-count n)
  (match n
    [#f 0]
    [(node _ _ l r) (+ (node-count l) (node-count r) 1)]))

(define (singleton x)
  (node 1 x #f #f))

(define (rank n)
  (match n
    [#f 0]
    [(node r _ _ _) r]))

(define (merge t1 t2 <=?)
  (match* (t1 t2)
    [(#f t) t]
    [(t #f) t]
    [((node _ k1 l r) (node _ k2 _ _))
     (cond [(<=? k1 k2)
            (define merged (merge r t2 <=?))
            (define rank-left (rank l))
            (define rank-right (rank merged))

            (cond [(>= rank-left rank-right)
                   (node (add1 rank-right) k1 l merged)]
                  [else
                   (node (add1 rank-left) k1 merged l)])]
           [else
            (merge t2 t1 <=?)])]))

(define (insert t x <=?)
  (merge t (singleton x) <=?))

(define *nothing* (gensym))

(define (get-min n)
  (match n
    ;[#f *nothing*]
    [(node _ x _ _) x]))

(define (remove-min n <=?)
  (match n
    [#f *nothing*]
    [(node _ _ l r) (merge l r <=?)]))


(provide/contract
 [leftist-tree (-> (-> any/c any/c any/c) list? leftist-tree?)]
 [leftist-tree? (-> any/c boolean?)]
 [leftist-tree-empty? (-> leftist-tree? boolean?)]
 [leftist-tree-count (-> leftist-tree/c exact-nonnegative-integer?)]
 [leftist-tree-add (-> leftist-tree/c any/c leftist-tree?)]
 [leftist-tree-add-all (-> leftist-tree? sequence? leftist-tree?)]
 [leftist-tree-min (-> leftist-tree/c any/c)]
 [leftist-tree-remove-min (-> leftist-tree/c leftist-tree?)] ; poz
 [leftist-tree->list (-> leftist-tree/c (listof any/c))]
 [in-leftist-tree (-> leftist-tree sequence?)])
