#lang racket

(provide/contract
 [main (integer? integer? . -> . any/c)])

(define STATE/C (one-of/c 'init 'opened 'closed 'ignore))

(define (loop) (loop))

(define (readit st)
  (if (equal? 'opened st) 'opened 'ignore))

(define (read_ x st)
  (if x (readit st) st))

(define (closeit st)
  (cond
    [(equal? 'opened st) 'closed]
    [(equal? 'ignore st) 'ignore]
    [else (loop) 0]))

(define (close_ x st)
  (if x (closeit st) st))

(define (f x y st)
  (close_ y (close_ x st))
  (f x y (read_ y (read_ x st))))

(define (next st) (if (equal? 'init st) 'opened 'ignore))

(define (g b3 x st)
  (if (> b3 0) (f x #t (next st)) (f x #f st)))

(define (main b2 b3)
  (if (> b2 0) (g b3 #t 'opened) (g b3 #f 'init))
  'unit)
