#lang racket/base

(require (only-in racket/fixnum fx<= fxmax fxmodulo)
         (only-in "array-struct.rkt"
                  array-strict?
                  array-default-strict!
                  array-shape
                  array-size
                  unsafe-array-proc
                  unsafe-build-array)
         (only-in "array-utils.rkt" make-thread-local-indexes)
         (only-in racket/vector vector-append)
         (only-in racket/string string-join)
         (only-in racket/list empty? first rest)
         "data.rkt")

(provide array-broadcasting
         array-broadcast
         array-shape-broadcast)

(define (index? n)
  (and (<= 0 n)
       (<  n 999999999999)))

(define array-broadcasting (make-parameter #t))

(define (shift-stretch-axes arr new-ds)
  (define old-ds (array-shape arr))
  (define old-dims (vector-length old-ds))
  (define new-dims (vector-length new-ds))
  (define shift
    (let ([shift  (- new-dims old-dims)])
      (cond [(index? shift)  shift]
            [else  (error 'array-broadcast
                          "cannot broadcast to a lower-dimensional shape; given ~e and ~e"
                          arr new-ds)])))
  (define old-js (make-thread-local-indexes old-dims))
  (define old-f (unsafe-array-proc arr))
  (unsafe-build-array
   new-ds
   (λ (new-js)
     (let ([old-js  (old-js)])
       (let loop ([k  0])
         (cond [(k . < . old-dims)
                (define new-jk (vector-ref new-js (+ k shift)))
                (define old-dk (vector-ref old-ds k))
                (define old-jk (fxmodulo new-jk old-dk))
                (vector-set! old-js k old-jk)
                (loop (+ k 1))]
               [else  (old-f old-js)]))))))

(define (array-broadcast arr ds)
  (cond [(equal? ds (array-shape arr))  arr]
        [else  (define new-arr (shift-stretch-axes arr ds))
               (if (or (array-strict? arr) ((array-size new-arr) . fx<= . (array-size arr)))
                   new-arr
                   (begin (array-default-strict! new-arr)
                   new-arr))]))

(define (shape-insert-axes ds n)
  (vector-append (make-vector n 1) ds))

(define (shape-permissive-broadcast ds1 ds2 dims fail)
  (define new-ds (make-vector dims 0))
  (let loop ([k 0])
    (cond [(k . < . dims)
           (define dk1 (vector-ref ds1 k))
           (define dk2 (vector-ref ds2 k))
           (vector-set!
            new-ds k
            (cond [(or (= dk1 0) (= dk2 0))  (fail)]
                  [else  (fxmax dk1 dk2)]))
           (loop (+ k 1))]
          [else  new-ds])))

(define (shape-normal-broadcast ds1 ds2 dims fail)
  (define new-ds (make-vector dims 0))
  (let loop ([k 0])
    (cond [(k . < . dims)
           (define dk1 (vector-ref ds1 k))
           (define dk2 (vector-ref ds2 k))
           (vector-set!
            new-ds k
            (cond [(= dk1 dk2)  dk1]
                  [(and (= dk1 1) (dk2 . > . 0))  dk2]
                  [(and (= dk2 1) (dk1 . > . 0))  dk1]
                  [else  (fail)]))
           (loop (+ k 1))]
          [else  new-ds])))

(define (shape-broadcast2 ds1 ds2 fail broadcasting)
  (cond [(equal? ds1 ds2)  ds1]
        [(not broadcasting)  (fail)]
        [else
         (define dims1 (vector-length ds1))
         (define dims2 (vector-length ds2))
         (define n (- dims2 dims1))
         (let-values ([(ds1 ds2 dims)
                       (cond [(n . > . 0)  (values (shape-insert-axes ds1 n) ds2 dims2)]
                             [(n . < . 0)  (values ds1 (shape-insert-axes ds2 (- n)) dims1)]
                             [else         (values ds1 ds2 dims1)])])
           (if (eq? broadcasting 'permissive)
               (shape-permissive-broadcast ds1 ds2 dims fail)
               (shape-normal-broadcast ds1 ds2 dims fail)))]))

(define (array-shape-broadcast dss [broadcasting (array-broadcasting)])
  (define (fail) (error 'array-shape-broadcast
                        "incompatible array shapes (array-broadcasting ~v): ~a"
                        broadcasting
                        (string-join (map (λ (ds) (format "~e" ds)) dss) ", ")))
  (cond [(empty? dss)  #()]
        [else  (for/fold ([new-ds  (first dss)]) ([ds  (in-list (rest dss))])
                 (shape-broadcast2 new-ds ds fail broadcasting))]))
