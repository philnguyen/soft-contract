#lang typed/racket/base

(provide sym-sub pretty n-sub unique-name next-neg!)
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

(: unique-name (∀ (X) ([Symbol] [#:subscript? Boolean] . ->* .
                       (case-> [→ (HashTable X Symbol)] ; for debugging only
                               [X → Symbol]))))
;; Return function that computes unique name with given prefix for each object.
;; No guarantee for consistency across different executions.
(define (unique-name prefix #:subscript? [subscript? #t])
  (let ([m : (HashTable X Symbol) (make-hash)]
        [f : (Integer → Any) (if subscript? n-sub values)])
    (case-lambda
      [() (for/hash : (HashTable X Symbol) ([(k v) m])
            (values k v))]
      [(x)
       (hash-ref! m x (λ () (string->symbol
                             (format "~a~a" prefix (f (hash-count m))))))])))

;; Generate the next unique negative integer
(define next-neg!
  (let ([n : Negative-Integer -1])
    (λ () : Negative-Integer
      (begin0 n (set! n (- n 1))))))
