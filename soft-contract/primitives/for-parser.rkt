#lang typed/racket/base

(provide prim-parse-result)

(require "def-prim-runtime.rkt"
         "prims.rkt" ; for side-effect
         )

(define prim-parse-result : (HashTable Symbol (Pairof (U 'quote 'const) Symbol)) (make-hasheq))

(for ([c (in-hash-keys const-table)])
  (hash-set! prim-parse-result c (cons 'const c)))

(for ([o (in-hash-keys prim-table)])
  (hash-set! prim-parse-result o (cons 'quote o)))

(for ([(x c) (in-hash alias-table)])
  (hash-set! prim-parse-result x
    (hash-ref prim-parse-result c
      (λ () (error 'alias-table "~a -> ~a but there's nothing" x c)))))

(for ([x (in-hash-keys alias-internal-table)])
  (hash-set! prim-parse-result x (cons 'const x)))
