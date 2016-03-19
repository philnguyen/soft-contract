#lang typed/racket/base

(provide (all-defined-out))
(require racket/pretty racket/string racket/port)
(require/typed/provide racket/syntax
  [format-symbol (String Any * → Symbol)])

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

(: suffixed-syms : Symbol Integer → (Listof Symbol))
;; Return list of `n` symbols suffixed by indices `[0..n-1]`
(define (suffixed-syms x n)
  (build-list n (λ ([i : Natural]) (format-symbol "~a~a" x (n-sub i)))))

;; Create generator for next natural/negative
(define (make-neg-src)
  (let ([n : Negative-Integer -1])
    (λ () : Negative-Integer
       (begin0 n (set! n (- n 1))))))
(define (make-nat-src)
  (let ([n : Natural 0])
    (λ () : Natural
       (begin0 n (set! n (+ n 1))))))
