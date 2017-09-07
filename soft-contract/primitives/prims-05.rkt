#lang typed/racket/base

(provide prims-05@)

(require racket/contract
         racket/set
         typed/racket/unit
         "def.rkt"
         "signatures.rkt")

(define-unit prims-05@
  (import prim-runtime^)
  (export)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;; 5.3 Structure Type Properties
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (def make-struct-type-property
    (case->
     [symbol? . -> . (values struct-type-property? procedure? procedure?)]
     [symbol? (or/c procedure? not 'can-impersonate) . -> . (values struct-type-property? procedure? procedure?)]
     [symbol? (or/c procedure? not 'can-impersonate) (listof (cons/c struct-type-property? (any/c . -> . any/c))) . -> . (values struct-type-property? procedure? procedure?)]
     [symbol? (or/c procedure? not 'can-impersonate) (listof (cons/c struct-type-property? (any/c . -> . any/c))) boolean? . -> . (values struct-type-property? procedure? procedure?)]))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;; 5.6 Structure Utilities
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (def-pred struct-type?))
