#lang typed/racket/base

(provide NeListof unzip-by unzip remove-duplicates)

(define-type (NeListof X) (Pairof X (Listof X)))

(: unzip-by (∀ (A X Y) (A → X) (A → Y) (Listof A) → (Values (Listof X) (Listof Y))))
;; Given a pair of functions, split list into 2
(define (unzip-by f g l)
  (for/lists ([xs : (Listof X)] [ys : (Listof Y)]) ([a : A l])
    (values (f a) (g a))))

(: unzip (∀ (X Y) (Listof (Pairof X Y)) → (Values (Listof X) (Listof Y))))
;; Unzip list of pairs into 2 lists
(define (unzip l)
  (unzip-by (inst car X Y) (inst cdr X Y) l))

(: remove-duplicates (∀ (X) (Listof X) → (Listof X)))
;; Can't re-use standard one, because parameteric contract messes with equality
(define (remove-duplicates xs)
  (define seen : (HashTable X #t) (make-hash))
  (for/list ([x xs] #:unless (hash-has-key? seen x))
    (hash-set! seen x #t)
    x))
