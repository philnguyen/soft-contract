#lang typed/racket/base

(provide (all-defined-out))

(require racket/set
         "../utils/set.rkt"
         "../runtime/definition.rkt"
         "../primitives/def-prim-runtime.rkt"
         "../primitives/prims.rkt" ; for side-effect
         "def-ext-runtime.rkt"
         "exts.rkt" ; for side-effect
         )

(define (get-defined-ext-names)
  ;; TODO def-opq table
  (∪ (list->seteq (hash-keys const-table))
     (list->seteq (hash-keys prim-table))
     (list->seteq (hash-keys alias-table))
     (list->seteq (hash-keys alias-internal-table))
     (list->seteq (hash-keys ext-table))))

;; range can't be:
;;  - `Syntaxof Any`, b/c can't convert to contract
;;  - `Any`, because TR doens't know how to wrap it
(: get-ext-parse-result : Symbol → (Values (U 'quote 'const) Symbol))
(define (get-ext-parse-result name)
  (cond [(hash-has-key? prim-table name) (values 'quote name)]
        [(hash-has-key? const-table name) (values 'const name)]
        [(hash-ref alias-table name #f) => get-ext-parse-result]
        [(hash-has-key? alias-internal-table name) (values 'const name)]
        [(hash-has-key? ext-table name) (values 'quote name)]
        [(hash-ref opq-table name #f) =>
         (λ ([V : -V])
           (error 'get-ext-parse-result "TODO: opq-table"))]
        [else (error 'get-ext-parse-result "`~a` not found" name)]))
