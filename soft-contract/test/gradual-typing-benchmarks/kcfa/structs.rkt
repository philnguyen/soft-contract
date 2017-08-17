#lang racket/base

(require racket/contract)

(provide
 Stx/c
 exp/c
 Call/c
 Ref/c
 Lam/c
 (contract-out
  [struct Stx ([label symbol?])]
  [struct exp ([label symbol?])]
  [struct Ref ([label symbol?] [var symbol?])]
  [struct Lam ([label symbol?]
               [formals (listof symbol?)]
               [call (or/c exp/c Call/c)])]
  [struct Call ([label symbol?]
                [fun (or/c exp/c Call/c)]
                [args (listof (or/c exp/c Call/c))])]))

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

(define Stx/c (struct/c Stx symbol?))
(define exp/c (struct/c exp symbol?))
(define Call/c (struct/c Call
                         symbol?
                         (or/c exp/c (recursive-contract Call/c #:chaperone))
                         (listof (or/c exp/c (recursive-contract Call/c #:chaperone)))))
(define Ref/c (struct/c Ref symbol? symbol?))
(define Lam/c (struct/c Lam symbol? (listof symbol?) (or/c exp/c Call/c)))
