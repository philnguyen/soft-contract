#lang typed/racket/base

(provide define-interner)

(require (for-syntax racket/base
                     racket/syntax
                     syntax/parse
                     ))

(define-syntax define-interner
  (syntax-parser
    [(_ T:id)
     (with-syntax ([⟪T⟫ (format-id #'T "⟪~a⟫" (syntax-e #'T))])
       #'(define-interner T #:interned-type-name ⟪T⟫))]
    [(_ T:id #:interned-type-name ⟪T⟫:id)
     (define T-name (syntax-e #'T))
     (define ⟪T⟫-name (syntax-e #'⟪T⟫))
     (define eq-type?
       (syntax-parse #'T
         [(~or (~literal Index) (~literal Fixnum) (~literal Symbol) (~literal Char))
          #t]
         [_ #f]))
     (with-syntax ([T->⟪T⟫ (format-id #'T "~a->~a" T-name ⟪T⟫-name)]
                   [⟪T⟫->T (format-id #'T "~a->~a" ⟪T⟫-name T-name)]
                   [count-⟪T⟫ (format-id #'T "count-~a" ⟪T⟫-name)]
                   [mk-m (if eq-type? #'make-hasheq #'make-hash)])
       #'(begin
           (define-new-subtype ⟪T⟫ (->⟪T⟫ Index))
           (define-values (T->⟪T⟫ ⟪T⟫->T count-⟪T⟫)
             (let ([m   : (HashTable T ⟪T⟫) (mk-m)]
                   [m⁻¹ : (HashTable ⟪T⟫ T) (make-hasheq)])
               (values
                (λ ([t : T]) : ⟪T⟫
                   (cond [(hash-ref m t #f) => values]
                         [else
                          (define ⟪t⟫ (->⟪T⟫ (hash-count m)))
                          (hash-set! m   t ⟪t⟫)
                          (hash-set! m⁻¹ ⟪t⟫ t)
                          ⟪t⟫]))
                (λ ([⟪t⟫ : ⟪T⟫]) : T
                  (hash-ref m⁻¹ ⟪t⟫ (λ () (error '⟪T⟫->T "nothing at ~a" ⟪t⟫))))
                (λ () : Index (hash-count m⁻¹)))))))]))
