#lang racket/base

(provide
  log2
  natural->bitstring
  bitstring->natural
  in-reach
)

;; -----------------------------------------------------------------------------

(require
  (only-in racket/math exact-ceiling)
  (only-in racket/format ~r)
  (only-in racket/list remove-duplicates)
)

;; =============================================================================

;; log, base 2
;; (: log2 (-> Integer Flonum))
(define (log2 n)
  (exact-ceiling (/ (log n) (log 2))))

;; Convert a natural number to a binary string, padded to the supplied width
;; (: natural->bitstring (-> Index #:pad Index String))
(define (natural->bitstring n #:pad pad-width)
  (and (exact-positive-integer? pad-width)
       (~r n #:base 2 #:min-width pad-width #:pad-string "0")))

;; Convert a binary string to a natural number
(define (bitstring->natural str)
  (define N (string-length str))
  (for/sum ([i (in-range N)])
    (define c (string-ref str (- N (add1 i))))
    (if (equal? #\1 c)
        (expt 2 i)
        0)))

;; Return all bitstrings reachable from `str`
;;  after incrementing at most `L` bits.
;; Result does NOT include the argument bitstring.
(define (in-reach str L)
  (cond [(zero? L) '()]
        [else
         (define res*
           (for/list ([i (in-range (string-length str))]
                      #:when (equal? #\0 (string-ref str i)))
             (define str+ (bitstring-flip str i))
             (cons str+ (in-reach str+ (sub1 L)))))
         (remove-duplicates (apply append res*) string=?)]))

;; Return a copy of `str` where the `i`-th bit is flipped.
;; (Flipped => 0 goes to 1 and 1 goes to 0)
(define (bitstring-flip str i)
  (define new (if (equal? #\0 (string-ref str i)) "1" "0"))
  (string-append (substring str 0 i)
                 new
                 (substring str (add1 i) (string-length str))))

