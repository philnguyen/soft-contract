#lang typed/racket/base

(provide get-defined-ext-names
         get-ext-parse-result)

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

         "ext-runtime.rkt"
         "../proof-relation/main.rkt"
         "../reduction/main.rkt"
         )

(define-unit pre-ext-for-parser@
  (import prim-runtime^ ext-runtime^)
  (export ext-for-parser^)

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
          [else (error 'get-ext-parse-result "`~a` not found" name)])))

(define-values/invoke-unit/infer
  (export ext-for-parser^ ext-runtime^ exts^)
  (link prims@ exts@ proof-system@ reduction@ pre-ext-for-parser@))
