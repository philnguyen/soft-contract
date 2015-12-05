#lang typed/racket/base

(provide unzip-by unzip)

(: unzip-by (∀ (A X Y) (A → X) (A → Y) (Listof A) → (Values (Listof X) (Listof Y))))
;; Given a pair of functions, split list into 2
(define (unzip-by f g l)
  (for/lists ([xs : (Listof X)] [ys : (Listof Y)]) ([a : A l])
    (values (f a) (g a))))

(: unzip (∀ (X Y) (Listof (Pairof X Y)) → (Values (Listof X) (Listof Y))))
;; Unzip list of pairs into 2 lists
(define (unzip l)
  (unzip-by (inst car X Y) (inst cdr X Y) l))
