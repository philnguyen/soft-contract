#lang racket/base

(provide (all-defined-out))

(require racket/set
         racket/match
         racket/list
         racket/splicing
         racket/string
         racket/syntax
         syntax/parse
         (prefix-in fake: "../fake-contract.rkt"))

(splicing-local
    ((define names '(call-with-input-file
                      call-with-output-file
                      open-input-file
                      open-output-file
                      file->list
                      file->value
                      with-input-from-file
                      with-output-to-file))
     (define (?recognized-name name)
       (define name-str (symbol->string name))
       (for/first ([s (in-list names)]
                   #:when (string-prefix? name-str (symbol->string s)))
         s)))
  (define-syntax-class indirect-app
    #:description "hack pattern for some `variable-reference-constant?` usages"
    #:literals (if #%plain-app #%variable-reference)
    (pattern (if (#%plain-app (~literal variable-reference-constant?)
                              (#%variable-reference f:id))
                 (#%plain-app g*:id _ ...)
                 (#%plain-app g:id x ...))
             #:attr fun-name (?recognized-name (syntax-e #'g))
             #:when (free-identifier=? #'f #'g)
             #:when (attribute fun-name)
             #:attr args #'(x ...))))

(splicing-local
    ((define names {seteq 'make-sequence
                          'in-list
                          'in-range
                          'in-hash
                          'in-hash-keys
                          'in-hash-values
                          'in-set
                          'in-vector
                          'in-naturals
                          })
     (define aliases (hasheq 'default-in-hash 'in-hash
                             'default-in-hash-keys 'in-hash-keys
                             'default-in-hash-values 'in-hash-values))
     (define (?private-id-name id)
       (if (set-member? names id)
           id
           (hash-ref aliases id #f))))
  (define-syntax-class private-id
    #:description "hack pattern for some private identifiers"
    (pattern x:id
             #:attr name (?private-id-name (syntax-e #'x))
             #:when (attribute name))))


(define-syntax-class scv-provide
  #:description "hacked scv provide form"
  #:literals (#%plain-app call-with-values #%plain-lambda)
  (pattern (#%plain-app
            call-with-values
            (#%plain-lambda ()
                            (#%plain-app (~literal fake:dynamic-provide/contract) prov ...))
            _)
           #:attr provide-list #'(prov ...)))
