#lang racket/base

(provide
  (struct-out Stx)
  (struct-out exp)
  (struct-out Ref)
  (struct-out Lam)
  (struct-out Call)
)

;; =============================================================================

(struct Stx
 (label ;: Symbol]))
))
(struct exp Stx ())

(struct Ref exp
 (var ;: Symbol]))
))
(struct Lam exp
 (formals ;: (Listof Symbol)]
  call ;: (U exp Ref Lam Call)]))
))
(struct Call Stx
 (fun ;: (U exp Ref Lam Call)]
  args ;: (Listof (U exp Ref Lam Call))]))
))
