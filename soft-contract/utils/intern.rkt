#lang typed/racket/base

(provide define-interner)

(require (for-syntax racket/base
                     racket/syntax
                     syntax/parse
                     ))

(define-syntax define-interner
  (syntax-parser
    [(_ T:id)
     (define T-name (syntax-e #'T))
     (with-syntax ([intern-T   (format-id #'T "intern-~a"   T-name)]
                   [unintern-T (format-id #'T "unintern-~a" T-name)]
                   [count-interned-T (format-id #'T "count-interned-~a" T-name)]
                   [Interned-T (format-id #'T "Interned-~a" T-name)])
       #'(begin
           (define-new-subtype Interned-T (->interned-T Nonnegative-Fixnum))
           (define-values (intern-T unintern-T count-interned-T)
             (let ([m   : (HashTable T Interned-T) (make-hash)]
                   [m⁻¹ : (HashTable Interned-T T) (make-hasheq)])
               (values
                (λ ([t : T]) : Interned-T
                   (cond [(hash-ref m t #f) => values]
                         [else
                          (define i (->interned-T (hash-count m)))
                          (hash-set! m   t i)
                          (hash-set! m⁻¹ i t)
                          i]))
                (λ ([i : Interned-T]) : T
                  (hash-ref m⁻¹ i))
                (λ () : Nonnegative-Fixnum (hash-count m⁻¹)))))))]))

(define-interner String)
