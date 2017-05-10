#lang racket

(provide
  left
  right
  up
  down
  grid-ref
  grid-height
  grid-width
  show-grid
  array-set!
  build-array
)

(require
  "../base/un-types.rkt"
  require-typed-check
  ;math/array ;; TODO it'd be nice to use this
)
(require (only-in "cell.rkt"
  char->cell%
  void-cell%
))

;; =============================================================================

(define (array-set! g p v)
  (vector-set! (vector-ref g (vector-ref p 0)) (vector-ref p 1) v))

(define (build-array p f)
  (for/vector
    ([x (in-range (vector-ref p 0))])
   (for/vector
                ([y (in-range (vector-ref p 1))])
    (f (vector (assert x index?) (assert y index?))))))
  ;(build-array p f)))

;; a Grid is a math/array Mutable-Array of cell%
;; (mutability is required for dungeon generation)

;; parses a list of strings into a grid, based on the printed representation
;; of each cell
(define (parse-grid los)
  (for/vector
              ; #:shape (vector (length los)
              ;                (apply max (map string-length los)))
              ;#:fill (new void-cell%)
              ([s (in-list los)])
            (for/vector
               ([c (in-string s)])
     (new (char->cell% c)))))

(define (show-grid g)
  (with-output-to-string
    (lambda ()
      (for ([r (in-vector g)])
        (for ([c (in-vector r)])
          (display (send c show)))
        (newline)))))

(define (grid-height g)
  (vector-length g))

(define (grid-width g)
  (vector-length (vector-ref g 0)))

(define (within-grid? g pos)
  (and (<= 0 (vector-ref pos 0) (sub1 (grid-height g)))
       (<= 0 (vector-ref pos 1) (sub1 (grid-width  g)))))

(define (grid-ref g pos)
  (and (within-grid? g pos)
       (vector-ref (vector-ref g (vector-ref pos 0)) (vector-ref pos 1))))

(define (left pos [n 1])
  (vector (vector-ref pos 0)
          (assert (- (vector-ref pos 1) n) index?)))

(define (right pos [n 1])
  (vector (vector-ref pos 0)
          (assert (+ (vector-ref pos 1) n) index?)))

(define (up pos [n 1])
  (vector (assert (- (vector-ref pos 0) n) index?)
          (vector-ref pos 1)))

(define (down pos [n 1])
  (vector (assert (+ (vector-ref pos 0) n) index?)
          (vector-ref pos 1)))


;(module+ test
;  (require typed/rackunit)
;
;  (: parse-and-show (-> (Listof String) String))
;  (define (parse-and-show los) (show-grid (parse-grid los)))
;  (: render-grid (-> (Listof String) String))
;  (define (render-grid g) (string-join g "\n" #:after-last "\n"))
;
;  (define g1
;    '(" "))
;  (check-equal? (parse-and-show g1) " \n")
;
;  (define g2
;    '("**********"
;      "*        *"
;      "*        *"
;      "*        *"
;      "**********"))
;  (check-equal? (parse-and-show g2) (render-grid g2))
;
;  (define g3 ; padding should work
;    '("**********"
;      "*        *"
;      "*        *"
;      "*        *"
;      "*****"))
;  (define g3*
;    '("**********"
;      "*        *"
;      "*        *"
;      "*        *"
;      "*****....."))
;  (check-equal? (parse-and-show g3) (render-grid g3*))
;
;  (define g2* (parse-grid g2))
;  (check-true (within-grid? g2* '#(0 0)))
;  (check-true (within-grid? g2* '#(0 1)))
;  (check-true (within-grid? g2* '#(1 0)))
;  (check-true (within-grid? g2* '#(4 4)))
;  (check-false (within-grid? g2* '#(0 10)))
;  (check-false (within-grid? g2* '#(5 0)))
;  (check-false (within-grid? g2* '#(5 10)))
;  )
