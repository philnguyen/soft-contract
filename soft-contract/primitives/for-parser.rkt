#lang typed/racket/base

(provide get-defined-prim-names
         get-prim-parse-result)

(require racket/set
         typed/racket/unit
         set-extras
         "../runtime/main.rkt"
         "../primitives/main.rkt"
         "main.rkt"
         "../reduction/signatures.rkt"
         "../primitives/signatures.rkt"
         "../signatures.rkt"
         "signatures.rkt"

         "prim-runtime.rkt"
         "../proof-relation/main.rkt"
         "../reduction/main.rkt"
         )

(define-unit pre-prims-for-parser@
  (import prim-runtime^)
  (export prims-for-parser^)

  (define (get-defined-prim-names)
    ;; TODO def-opq table
    (∪ (list->seteq (hash-keys const-table))
       (list->seteq (hash-keys prim-table))
       (list->seteq (hash-keys alias-table))))

  ;; range can't be:
  ;;  - `Syntaxof Any`, b/c can't convert to contract
  ;;  - `Any`, because TR doens't know how to wrap it
  (: get-prim-parse-result : Symbol → (Values (U 'quote 'const) Symbol))
  (define (get-prim-parse-result name)
    (cond [(hash-has-key? prim-table name) (values 'quote name)]
          [(hash-has-key? const-table name) (values 'const name)]
          [(hash-ref alias-table name #f) => get-prim-parse-result]
          [(hash-ref opq-table name #f) =>
           (λ ([V : -V])
             (error 'get-prim-parse-result "TODO: opq-table"))]
          [else (error 'get-prim-parse-result "`~a` not found" name)])))

(define-values/invoke-unit/infer
  (export prims-for-parser^ prims^)
  (link prims@ proof-system@ reduction@ pre-prims-for-parser@))
