#lang racket/base
(require racket/contract racket/set redex/reduction-semantics)

(provide (all-defined-out))

;; Return number as subscript string
(define/contract (n-sub n)
  (integer? . -> . string?)
  (cond
   [(< n 0) (format "₋~a" (n-sub (- n)))]
   [(<= n 9) (substring "₀₁₂₃₄₅₆₇₈₉" n (+ n 1))]
   [else
    (define-values (q r) (quotient/remainder n 10))
    (string-append (n-sub q) (n-sub r))]))

;; Return a bijection between `X` and `Symbol`.
;; No guarantee for consistency between different executions.
(define/contract (unique-name prefix)
  (symbol? . -> . (values (any/c . -> . symbol?) (symbol? . -> . any)))
  (define m   (make-hash))
  (define m⁻¹ (make-hasheq))
  (values
   (λ (x)
     (hash-ref! m x
                (λ ()
                  (define y (string->symbol (format "~a~a" prefix (n-sub (hash-count m)))))
                  (hash-set! m⁻¹ y x)
                  y)))
   (λ (y) (hash-ref m⁻¹ y))))

;; Create a bit-set. No guarantee about consistency across multiple program runs.
(define/contract (make-bitset)
  ;; Parametric contract screws this up...
  (-> (values (exact-nonnegative-integer? any/c . -> . exact-nonnegative-integer?)
              (exact-nonnegative-integer? any/c . -> . boolean?)
              (exact-nonnegative-integer? . -> . (listof any/c))))

  (define m   (make-hash))
  (define m⁻¹ (make-hasheq))

  (define (x->ith x)
    (hash-ref! m x (λ ()
                     (define i (hash-count m))
                     (hash-set! m⁻¹ i x)
                     i)))

  (define (ith->x i)
    (hash-ref m⁻¹ i (λ () (error 'ith⁻¹ "No element indexed ~a" i))))

  (define (bs->xs bs)
    (for/list ([i (integer-length bs)] #:when (bitwise-bit-set? bs i))
      (ith->x i)))

  (define (add bs x) (bitwise-ior bs (arithmetic-shift 1 (x->ith x))))

  (define (has? bs x) (bitwise-bit-set? bs (x->ith x)))
  
  (values add has? bs->xs))

(define-language mt
  [collection set (any ...)]
  [set (side-condition (name set any) (set? (term set)))])

(define-judgment-form mt
  #:contract (∈ any collection)
  #:mode     (∈ O   I         )
  [(where (_ ... any _ ...) ,(set->list (term set)))
   -----------------------------------------
   (∈ any set)]
  [(∈ any (_ ... any _ ...))])
