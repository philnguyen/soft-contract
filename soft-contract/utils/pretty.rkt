#lang typed/racket/base

(provide sym-sub pretty n-sub unique-name next-neg! next-nat!)
(require racket/pretty racket/string racket/port)

(: sym-sub : Symbol → Symbol)
;; Make all digits in symbol subscripts
(define (sym-sub x)
  (string->symbol
   (list->string
    (for/list ([c (in-string (symbol->string x))])
      (case c
        [(#\0) #\₀] [(#\1) #\₁] [(#\2) #\₂] [(#\3) #\₃] [(#\4) #\₄]
        [(#\5) #\₅] [(#\6) #\₆] [(#\7) #\₇] [(#\8) #\₈] [(#\9) #\₉]
        [else c])))))

(: pretty : Any → String)
;; Pretty print given object
(define (pretty x)
  (parameterize ([pretty-print-columns 80])
    (string-trim (with-output-to-string (λ () (pretty-display x))))))

(: n-sub : Integer → String)
;; Return number as subscript string
(define (n-sub n)
  (cond
   [(< n 0) (format "₋~a" (n-sub (- n)))]
   [(<= n 9) (substring "₀₁₂₃₄₅₆₇₈₉" n (+ n 1))]
   [else
    (define-values (q r) (quotient/remainder n 10))
    (string-append (n-sub q) (n-sub r))]))

(: unique-name (∀ (X) ([Symbol] [#:subscript? Boolean] . ->* . (Values (X → Symbol) (Symbol → X)))))
;; Return function that computes unique name with given prefix for each object.
;; No guarantee for consistency across different executions.
(define (unique-name prefix #:subscript? [subscript? #t])
  (define m : (HashTable X Symbol) (make-hash))
  (define m⁻¹ : (HashTable Symbol X) (make-hasheq))
  (define f : (Integer → Any) (if subscript? n-sub values))
  (values
   (λ (x)
     (hash-ref! m x
                (λ ()
                  (define y (string->symbol (format "~a~a" prefix (f (hash-count m)))))
                  (hash-set! m⁻¹ y x)
                  y)))
   (λ (y) (hash-ref m⁻¹ y))))

;; Generate the next unique negative integer
(define next-neg!
  (let ([n : Negative-Integer -1])
    (λ () : Negative-Integer
      (begin0 n (set! n (- n 1))))))

(define next-nat!
  (let ([n : Natural 0])
    (λ () : Natural
       (begin0 n (set! n (+ n 1))))))
