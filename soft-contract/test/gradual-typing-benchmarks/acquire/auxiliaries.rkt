#lang racket/base

(provide
  randomly-pick
  ;; (-> cons? any)

  distinct
  ;; (-> list? boolean?)
  ;; for small lists O(n^2)

  (rename-out [ext:aux:partition aux:partition])
  ;; (->* [(Listof Any) (-> Any Real)] [#:info (-> Any Any)] (Listof (Listof Any)))
  ;; Precondition: input list is sorted vis <= or >=
)

;; -----------------------------------------------------------------------------

(require
  (only-in racket/list
    first second
    rest range cons?)
)

;; ---------------------------------------------------------------------------------------------------

(define (randomly-pick l)
  (list-ref l (random (length l))))

(define (ext:aux:partition lo-h-size selector info)
  (define s* (map selector lo-h-size))
  (define s1 (sort s* <=))
  (define s2 (sort s* <=))
  (unless (or (equal? s* s1) (equal? s* s2))
    (error 'aux:partition "Precondition: expected a sorted list"))
  (aux:partition lo-h-size selector info))

(define (aux:partition lo-h-size selector info)
  (define one (first lo-h-size))
  (let loop
       [(pred (selector one))
        (l    (rest lo-h-size))
        [pt   (list (info one))]]
    (cond
      [(null? l) (list (reverse pt))]
      [else 
       (define two (first l))
       (if (not (= (selector two) pred))
           (cons (reverse pt) (loop (selector two) (rest l) (list (info two))))
           (loop pred (rest l) (cons (info two) pt)))])))

(define (distinct s)
  (cond
    [(null? s) #t]
    [else (and (not (member (first s) (rest s))) (distinct (rest s)))]))
