#lang racket/base

(provide expand/high-level-contracts)

(require racket/base
         racket/match
         racket/pretty
         racket/syntax
         syntax/parse
         syntax/parse/define
         syntax/id-table
         macro-debugger/expand
         racket/contract
         (prefix-in f: soft-contract/fake-contract)
         (for-syntax racket/base
                     racket/syntax
                     syntax/parse
                     ))

;; It seems neccessary to substitute contract forms ourselves.
;; Otherwise at the time of requiring `soft-contract/fake-contract`,
;; expansion will have already resolved them to those the original `racket/contract`.
(define swap-table (make-free-id-table #:phase #f))
(let ([add! (λ (i1 i2) (free-id-table-set! swap-table i1 i2))]) 
  (add! #'provide #'f:provide)
  (add! #'provide/contract #'f:provide/contract)
  (add! #'contract-out #'f:contract-out)
  ;(add! #'struct #'f:struct)
  (add! #'-> #'f:->)
  (add! #'->i #'f:->i)
  (add! #'->* #'f:->*)
  (add! #'case-> #'f:case->)
  (add! #'any/c #'f:any/c)
  (add! #'any #'f:any)
  (add! #'hash/c #'f:hash/c)
  (add! #'set/c #'f:set/c)
  (add! #'none/c #'f:none/c)
  (add! #'false/c #'f:false/c)
  (add! #'and/c #'f:and/c)
  (add! #'or/c #'f:or/c)
  (add! #'not/c #'f:not/c)
  (add! #'list/c #'f:list/c)
  (add! #'listof #'f:listof)
  (add! #'vector/c #'f:vector/c)
  (add! #'vectorof #'f:vectorof)
  (add! #'cons/c #'f:cons/c)
  (add! #'box/c #'f:box/c)
  (add! #'struct/c #'f:struct/c)
  (add! #'one-of/c #'f:one-of/c)
  (add! #'=/c #'f:=/c)
  (add! #'>/c #'f:>/c)
  (add! #'>=/c #'f:>=/c)
  (add! #'</c #'f:</c)
  (add! #'<=/c #'f:<=/c)
  (add! #'recursive-contract #'f:recursive-contract)
  (add! #'between/c #'f:between/c)
  (add! #'flat-contract #'f:flat-contract)
  (add! #'define/contract #'f:define/contract)
  )

(define (expand/high-level-contracts stx)
  (define stop-list (list* #'#%require (free-id-table-keys swap-table)))
  ;; TODO If I expand/hide first with this stop-list,
  ;; Somehow `->` is retained, but all the `provide` stuff is gone
  ;; (expand (sneak-fake-contracts-into (expand/hide stx stop-list)))
  (expand (sneak-fake-contracts-into stx)))

(define (sneak-fake-contracts-into stx)
  (define-values (stx* faked?) (replace-identifiers stx))
  (if faked? stx* (insert-fake-contract-require stx*)))

(define (replace-identifiers stx)
  (define faked? #f)

  (define (go stx)
    (match stx
      [(? identifier? i)
       (syntax-parse i
         [(~or (~literal racket/contract) (~literal soft-contract/fake-contract))
          (set! faked? #t)
          #'soft-contract/fake-contract]
         [_
          ;; TODO restore source location information?
          (free-id-table-ref swap-table i (λ () i))])]
      [(cons p q) (cons (go p) (go q))]
      [(and (? syntax?) (app syntax-e e))
       (datum->syntax stx (go e)
                      (list (syntax-source stx)
                            (syntax-line stx)
                            (syntax-column stx)
                            (syntax-position stx)
                            (syntax-span stx)))]
      [_ stx]))

  (define stx* (go stx)) ; important to call `(go _)` before checking `faked?`
  (values stx* faked?))

(define insert-fake-contract-require
  (syntax-parser
    [(module id path (#%plain-module-begin form ...))
     (define/with-syntax require (datum->syntax #'id 'require)) ; ambiguous otherwise
     #'(module id path
         (#%plain-module-begin
          (require soft-contract/fake-contract)
          form ...))]
    [form #'form]))
