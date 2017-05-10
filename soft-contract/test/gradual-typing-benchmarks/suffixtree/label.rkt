#lang racket/base

(require
  "data.rkt")
;; Label implementation.  Labels are like strings, but also allow for
;; efficient shared slicing.
;;
;; TODO later: see if we can generalize labels to be more than just
;; text strings.  It might be useful to have them as arbitrary
;; elements, perhaps as vectors?

;; FIXME: set custom writer for labels to be displayed for debugging
;; purposes.
;; (http://download.plt-scheme.org/doc/299.400/html/mzscheme/mzscheme-Z-H-11.html#node_sec_11.2.10)


;; label-element? object -> true
;; Every value is considered to be a possible label-element.
(define (label-element? obj) #t)

;; When comparing label elements, we use equal?.
;;
(define label-element-equal? equal?)


(provide
         (rename-out [ext:make-label make-label])
         label-element?
         label-element-equal?
         string->label
         string->label/with-sentinel
         vector->label
         vector->label/with-sentinel
         label->string
         label->string/removing-sentinel
         label->vector
         label-length
         label-ref
         sublabel
         sublabel!
         label-prefix?
         label-equal?
         label-empty?
         label-copy
         label-ref-at-end?
         label-source-id
         label-same-source?)


;; make-label: label-element -> label
;; Constructs a new label from either a string or a vector of things.
(define (ext:make-label label-element)
  (cond ((string? label-element) (string->label label-element))
        ((vector? label-element) (vector->label label-element))
        (else
         (error 'make-label "Don't know how to make label from ~S" label-element))))


(define (make-sentinel)
  (gensym 'sentinel))

(define (sentinel? datum)
  (symbol? datum))

;; vector->label vector
;; Constructs a new label from the input vector.
(define (vector->label vector)
  (make-label (vector->immutable-vector vector)
              0 (vector-length vector)))


;; vector->label vector
;; Constructs a new label from the input vector, with a sentinel
;; symbol at the end.
(define (vector->label/with-sentinel vector)
  (let* ((N (vector-length vector))
         (V (make-vector (add1 N))))
    (vector-set! V N (make-sentinel))
    (let loop ((i 0))
      (if (< i N)
          (begin (vector-set! V i (vector-ref vector i))
                 (loop (add1 i)))
          (vector->label V)))))


;; string->label: string -> label
;; Constructs a new label from the input string.
(define string->label
  (let ((f (compose vector->label list->vector string->list)))
    (lambda (str) (f str))))


;; string->label/with-sentinel: string -> label
;; Constructs a new label from the input string, attaching a unique
;; sentinel symbol at the end of the label.
;;
;; Note: this label can not be converted in whole back to a string:
;; the sentinel character interferes with string concatenation
(define string->label/with-sentinel
  (let ((f (compose vector->label/with-sentinel list->vector string->list)))
    (lambda (str) (f str))))


;; label-length: label -> number?
;; Returns the length of the label.
(define (label-length label)
  (- (label-j label) (label-i label)))


;; label-ref: label number? -> char
;; Returns the kth element in the label.
(define (label-ref label k)
  (vector-ref (label-datum label) (+ k (label-i label))))


;; sublabel: label number number -> label
;; Gets a slice of the label on the half-open interval [i, j)
(define sublabel
  (case-lambda
    ((label i)
     (sublabel label i (label-length label)))
    ((label i j)
     (unless (<= i j)
       (error 'sublabel "illegal sublabel [~a, ~a]" i j))
     (make-label (label-datum label)
                 (+ i (label-i label))
                 (+ j (label-i label))))))


;; sublabel!: label number number -> void
;; destructively sets the input label to sublabel.
(define sublabel!
  (case-lambda
    ((label i)
     (sublabel! label i (label-length label)))
    ((label i j)
     (begin
       ;; order dependent code ahead!
       (set-label-j! label (+ j (label-i label)))
       (set-label-i! label (+ i (label-i label)))
       (void)))))


;; label-prefix?: label label -> boolean
;; Returns true if the first label is a prefix of the second label
(define (label-prefix? prefix other-label)
  (let ((m (label-length prefix))
        (n (label-length other-label)))
    (if (> m n)                       ; <- optimization: prefixes
					; can't be longer.
        #f
        (let loop ((k 0))
          (if (= k m)
              #t
              (and (equal? (label-ref prefix k) (label-ref other-label k))
                   (loop (add1 k))))))))


;; label-equal?: label label -> boolean
;; Returns true if the two labels are equal.
(define (label-equal? l1 l2)
  (and (= (label-length l1) (label-length l2))
       (label-prefix? l1 l2)))


;; label-empty?: label -> boolean
;; Returns true if the label is considered empty
(define (label-empty? label)
  (>= (label-i label) (label-j label)))


;; label->string: label -> string
;; Extracts the string that the label represents.
;; Precondition: the label must have originally come from a string.
;; Note: this operation is expensive: don't use it except for debugging.
(define (label->string label)
  (list->string (vector->list (label->vector label))))


(define (label->string/removing-sentinel label)
  (let* ([ln (label-length label)]
         [N (if (and (> ln 0) (sentinel? (label-ref label (sub1 ln))))
                (sub1 ln)
                ln)])
    (build-string N (lambda (i) (label-ref label i)))))


;; label->vector: label -> vector
;; Extracts the vector that the label represents.
;; Note: this operation is expensive: don't use it except for debugging.
(define (label->vector label)
  (let* ((N (label-length label))
         (buffer (make-vector N)))
    (let loop ((i 0))
      (if (< i N)
          (begin
            (vector-set! buffer i (label-ref label i))
            (loop (add1 i)))
          (vector->immutable-vector buffer)))))


;; label-copy: label->label
;; Returns a copy of the label.
(define (label-copy label)
  (make-label (label-datum label) (label-i label) (label-j label)))


;; label-ref-at-end?: label number -> boolean
(define (label-ref-at-end? label offset)
  (= offset (label-length label)))


;; label-source-id: label -> number
(define (label-source-id label)
  (eq-hash-code (label-datum label)))

;; label-same-source?: label label -> boolean
(define (label-same-source? label-1 label-2)
  (eq? (label-datum label-1) (label-datum label-2)))

;; --- from suffixtree.rkt
(provide label-source-eq?)
(define label-source-eq? label-same-source?)
