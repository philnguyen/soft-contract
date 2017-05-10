#lang racket/base

(provide
  slice-at
  break-at
  slicef-after
  shifts
)

;; -----------------------------------------------------------------------------

(require
  (only-in racket/list split-at empty empty? first take-right make-list drop-right take drop)
)
;; =============================================================================

(define slice-at
  ;; with polymorphic function, use cased typing to simulate optional position arguments 
  (case-lambda
    [(xs len)
     (slice-at xs len #f)]
    [(xs len force?)
     (define-values (last-list list-of-lists)
       (for/fold ([current-list '()][list-of-lists  '()])
                  ([x (in-list xs)][i (in-naturals)])
         (if (= (modulo (add1 i) len) 0)
             (values '() (cons (reverse (cons x current-list)) list-of-lists))
             (values (cons x current-list) list-of-lists))))
     (reverse (if (or (eq? '() last-list) (and force? (not (= len (length last-list)))))
                  list-of-lists
                  (cons (reverse last-list) list-of-lists)))]))

(define (break-at xs bps)
  (let ([bps (if (list? bps) bps (list bps))]) ; coerce bps to list
    (when (ormap (λ(bp) (>= bp (length xs))) bps)
      (error 'break-at (format "breakpoint in ~v is greater than or equal to input list length = ~a" bps (length xs))))
    ;; easier to do back to front, because then the list index for each item won't change during the recursion
    ;; cons a zero onto bps (which may already start with zero) and then use that as the terminating condition
    ;; because breaking at zero means we've reached the start of the list
    (reverse (let loop ([xs xs][bps (reverse (cons 0 bps))])
               (if (= (car bps) 0)
                   (cons xs null) ; return whatever's left, because no more splits are possible
                   (let-values ([(head tail) (split-at xs (car bps))])
                     (cons tail (loop head (cdr bps)))))))))

(define (slicef-after xs pred)
  (define-values (last-list list-of-lists)
    (for/fold ([current-list empty][list-of-lists empty])
               ([x (in-list xs)])
      (if (pred x)
          (values empty (cons (reverse (cons x current-list)) list-of-lists))
          (values (cons x current-list) list-of-lists))))
  (reverse (if (empty? last-list)
               list-of-lists
               (cons (reverse last-list) list-of-lists))))

(define shifts
  (case-lambda
    [(xs how-fars)
     (shifts xs how-fars #f #f)]
    [(xs how-fars fill-item)
     (shifts xs how-fars fill-item #f)]
    [(xs how-fars fill-item cycle)
     (map (λ(how-far) (shift xs how-far fill-item cycle)) how-fars)]))

(define shift
  (case-lambda
    [(xs how-far)
     (shift xs how-far #f #f)]
    [(xs how-far fill-item)
     (shift xs how-far fill-item #f)]
    [(xs how-far fill-item cycle)
     (define abs-how-far (abs how-far))
     (cond 
       [(> abs-how-far (length xs)) (error 'shift "index is too large for list\nindex: ~a\nlist: ~v" how-far xs)]
       [(= how-far 0) xs]
       [(positive? how-far)
        (define filler (if cycle
                           (take-right xs abs-how-far)
                           (make-list abs-how-far fill-item)))
        (append filler (drop-right xs abs-how-far))]
       [else ; how-far is negative
        (define filler (if cycle
                           (take xs abs-how-far)
                           (make-list abs-how-far fill-item)))
        (append (drop xs abs-how-far) filler)])]))
