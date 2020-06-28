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
         "utils.rkt"
         (for-syntax racket/base
                     racket/syntax
                     syntax/parse
                     ))

;; It seems neccessary to substitute contract forms ourselves.
;; Otherwise at the time of requiring `soft-contract/fake-contract`,
;; expansion will have already resolved them to those the original `racket/contract`.
(define swap-table (make-free-id-table #:phase #f))
(let ([add! (λ (i1 i2) (free-id-table-set! swap-table i1 i2))])
  (add! #'define #'f:define)
  (add! #'provide #'f:provide)
  (add! #'provide/contract #'f:provide/contract)
  (add! #'contract-out #'f:contract-out)
  ;(add! #'struct #'f:struct)
  (add! #'-> #'f:->)
  (add! #'->i #'f:->i)
  (add! #'->* #'f:->*)
  (add! #'parametric->/c #'f:parametric->/c)
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
  (add! #'parameter/c #'f:parameter/c)
  (add! #'flat-contract #'f:flat-contract)
  (add! #'define/contract #'f:define/contract)
  (add! #'contract? #'f:contract?)
  )

(define swap-identifiers? (make-parameter #t))

(define (expand/high-level-contracts stx)
  ;(define stop-list (list* #'#%require (free-id-table-keys swap-table)))
  ;; TODO If I expand/hide first with this stop-list,
  ;; Somehow `->` is retained, but all the `provide` stuff is gone
  ;; (expand (sneak-fake-contracts-into (expand/hide stx stop-list)))
  (expand (sneak-fake-contracts-into stx)))

(define (sneak-fake-contracts-into stx)
  (define faked? (make-parameter #f))

  (define go
    (syntax-parser
      [(~or #;(~literal racket/contract) (~literal soft-contract/fake-contract))
       (set-box! (faked?) #t)
       #'soft-contract/fake-contract]
      ;; TODO restore source location information?
      [i:id (if (swap-identifiers?)
                (free-id-table-ref swap-table #'i (λ () #'i))
                #'i)]
      [e (with-syntax-source #'e (go-e (syntax-e #'e)))]))

  (define go-e
    (match-lambda
      [(cons p q)
       ;; `syntax-parse` and `~literal` didn't work :(
       (cond [(and (identifier? p) #|HACK|# (eq? 'module (syntax-e p)))
              (parameterize ([faked? (box #f)])
                (define p* (go-e p))
                (define q* (go-e q))
                (cons p*
                      (if (unbox (faked?))
                          q*
                          (syntax-parse q*
                            [(id path (#%plain-module-begin form ...))
                             (with-syntax ([require (datum->syntax #'id 'require)])
                               (list #'id #'path
                                     #'(#%plain-module-begin
                                        (require soft-contract/fake-contract)
                                        form ...)))]
                            [(id path form ...)
                             (with-syntax ([require (datum->syntax #'id 'require)])
                               (list* #'id #'path #'(require soft-contract/fake-contract)
                                      (syntax->list #'(form ...))))]))))]
             [(and (identifier? p) #|HACK|# (eq? 'except-in (syntax-e p)))
              (parameterize ([swap-identifiers? #f])
                (cons (go-e p) (go-e q)))]
             [else (cons (go-e p) (go-e q))])]
      [(? syntax? s) (go s)]
      [x x]))

  (go stx))
