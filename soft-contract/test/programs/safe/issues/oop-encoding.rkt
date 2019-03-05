#lang racket

(define posn/c
  (->i ([msg (one-of/c 'x 'y 'posn 'move-toward/speed 'dist)])
       (res (msg)
            (cond
              [(equal? msg 'x) (-> real?)]
              [(equal? msg 'y) (-> real?)]
              [(equal? msg 'posn) (-> posn/c)]
              [(equal? msg 'move-toward/speed) (posn/c real? . -> . posn/c)]
              [(equal? msg 'dist) (posn/c . -> . real?)]
              [else "error"]))))

(define (new-posn x y)
  (letrec ([this
            (λ (msg)
              (cond
                [(equal? msg 'x) (λ () x)]
                [(equal? msg 'y) (λ () y)]
                [(equal? msg 'posn) (λ () this)]
                [(equal? msg 'move-toward/speed)
                 (λ (p speed)
                   (let* ([δx (- ((p 'x)) x)]
                          [δy (- ((p 'y)) y)]
                          [move-distance (min speed (max (abs δx) (abs δy)))])
                     (cond
                       [(< (abs δx) (abs δy))
                        ((this 'move)
                         0
                         (if (positive? δy) move-distance (- 0 move-distance)))]
                       [else
                        ((this 'move)
                         (if (positive? δx) move-distance (- 0 move-distance))
                         0)])))]
                [(equal? msg 'move)
                 (λ (δx δy) (new-posn (+ x δx) (+ y δy)))]
                [(equal? msg 'dist)
                 (λ (p)
                   (sqrt (+ (sqr (- ((p 'y)) y))
                            (sqr (- ((p 'x)) x)))))]
                [else "unknown message"]))])
    this))

(provide
 (contract-out
  [new-posn (real? real? . -> . posn/c)]))
