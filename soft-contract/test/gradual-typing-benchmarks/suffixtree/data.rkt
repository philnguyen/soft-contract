#lang racket/base

(require racket/contract)

(provide
 label/c
 node/c
 suffix-tree/c
 (contract-out
  [struct label ([datum (vectorof (or/c char? symbol?))] [i exact-nonnegative-integer?] [j exact-nonnegative-integer?])]
  [struct suffix-tree ([root node/c])]
  [struct node ([up-label label/c] [parent (or/c not node/c)] [children {listof node/c}] [suffix-link (or/c not node/c)])]))


(define-struct label (datum i j) #:mutable)

;; A suffix tree consists of a root node.
(define-struct suffix-tree (root))

;; up-label: label
;; parent: (union #f node)
;; children: (listof node)
;; suffix-link: (union #f node)
(define-struct node (up-label parent children suffix-link) #:mutable)

(define label/c (struct/c label (vectorof (or/c char? symbol?)) exact-nonnegative-integer? exact-nonnegative-integer?))
(define node/c (struct/c node
                         label/c
                         (or/c not (recursive-contract node/c #:chaperone))
                         (listof (recursive-contract node/c #:chaperone))
                         (or/c not (recursive-contract node/c #:chaperone))))
(define suffix-tree/c (struct/c suffix-tree node/c))

