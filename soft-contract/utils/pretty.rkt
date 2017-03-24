#lang typed/racket/base

(provide (all-defined-out))
(require racket/pretty racket/string racket/port)
(require/typed/provide racket/syntax
  [format-symbol (String (U String Symbol Identifier Keyword Char Number) * → Symbol)])

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

;; Return superscript and subscript for given number
(define-values (n-sub n-sup)
  (let ([subs : (Vectorof Symbol) #(₀ ₁ ₂ ₃ ₄ ₅ ₆ ₇ ₈ ₉)]
        [sups : (Vectorof Symbol) #(⁰ ¹ ² ³ ⁴ ⁵ ⁶ ⁷ ⁸ ⁹)])
    (: with-digits : Symbol (Vectorof Symbol) → Integer → Symbol)
    (define (with-digits neg ds)
      (: go : Natural → Symbol)
      (define (go n)
        (cond
          [(<= n 9) (vector-ref ds n)]
          [else
           (define-values (q r) (quotient/remainder n 10))
           (format-symbol "~a~a" (go q) (go r))]))
      (λ (n)
        (if (>= n 0)
            (go n)
            (format-symbol "~a~a" neg (go (- n))))))
    (values (with-digits '₋ subs) (with-digits '⁻ sups))))

(: suffixed-syms : Symbol Integer → (Listof Symbol))
;; Return list of `n` symbols suffixed by indices `[0..n-1]`
(define (suffixed-syms x n)
  (build-list n (λ ([i : Natural]) (format-symbol "~a~a" x (n-sub i)))))
