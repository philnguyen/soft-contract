#lang typed/racket/base

(provide (all-defined-out))

(require racket/set
         "../utils/set.rkt"
         "../runtime/definition.rkt"
         "def-prim-runtime.rkt"
         "prims.rkt" ; for side-effect
         )

(define (get-defined-prim-names)
  ;; TODO def-opq table
  (∪ (list->seteq (hash-keys const-table))
     (list->seteq (hash-keys prim-table))
     (list->seteq (hash-keys alias-table))
     (list->seteq (hash-keys alias-internal-table))))

;; range can't be:
;;  - `Syntaxof Any`, b/c can't convert to contract
;;  - `Any`, because TR doens't know how to wrap it
(: get-prim-parse-result : Symbol → (Values (U 'quote 'const) Symbol))
(define (get-prim-parse-result name)
  (cond [(hash-has-key? prim-table name) (values 'quote name)]
        [(hash-has-key? const-table name) (values 'const name)]
        [(hash-ref alias-table name #f) => get-prim-parse-result]
        [(hash-has-key? alias-internal-table name) (values 'const name)]
        [(hash-ref opq-table name #f) =>
         (λ ([V : -V])
           (error 'get-prim "TODO: opq-table"))]
        [else (error 'get-prim-parse-result "~a" name)]))
