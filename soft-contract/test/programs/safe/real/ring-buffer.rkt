#lang racket/base
(require racket/match
         racket/contract)

(define (wrap-at max i)
  (if (i . >= . max)
      (wrap-at max (- i max))
      i))
(define (wrap+ max x y)
  (wrap-at max (+ x y))) 

(define-struct ring-buffer (length [fst #:mutable] [nxt #:mutable] vals)
  #:property prop:sequence
  (lambda (rb)
    (match rb
      [(struct ring-buffer (max fst _ vals))
       (make-do-sequence
        (lambda ()
          (values 
           (lambda (p) 
             (ring-buffer-ref rb p))
           (lambda (p) (add1 p))
           0
           (lambda (p) (< p max))
           (lambda (v) v)
           (lambda (p v) (and (< p max) v)))))])))

(define (empty-ring-buffer max)
  (make-ring-buffer max #f 0 (make-vector max #f)))
(define (ring-buffer-push! rb m)
  (match rb
    [(struct ring-buffer (max fst nxt vals))
     (unless (zero? max)
       (when (and fst (= fst nxt))
         (set-ring-buffer-fst! rb (wrap+ max (ring-buffer-fst rb) 1)))
       (vector-set! vals nxt m)
       (set-ring-buffer-nxt! rb (wrap+ max nxt 1))       
       (unless fst
         (set-ring-buffer-fst! rb 0)))]))

(define (ring-buffer-ref rb i)
  (match rb
    [(struct ring-buffer (max fst _ vals))
     (vector-ref vals (wrap+ max (if fst fst 0) i))]))
(define (ring-buffer-set! rb i v)
  (match rb
    [(struct ring-buffer (max fst _ vals))
     (vector-set! vals (wrap+ max (if fst fst 0) i) v)]))

(provide/contract
 [empty-ring-buffer (exact-nonnegative-integer? . -> . ring-buffer?)]
 [ring-buffer? (any/c . -> . boolean?)]
 [ring-buffer-length (ring-buffer? . -> . exact-nonnegative-integer?)]
 [ring-buffer-ref (ring-buffer? exact-nonnegative-integer? . -> . (or/c any/c false/c))]
 [ring-buffer-set! (ring-buffer? exact-nonnegative-integer? (and/c any/c (not/c false/c)) . -> . void)]
 [ring-buffer-push! (ring-buffer? (and/c any/c (not/c false/c)) . -> . void)])
