#lang typed/racket/base

(provide (all-defined-out))

; https://github.com/racket/typed-racket/blob/master/typed-racket-lib/typed-racket/base-env/base-special-env.rkt#L18-L27
(: make-template-identifier : Symbol Module-Path → Identifier)
(define (make-template-identifier what where)
  (let ([name (module-path-index-resolve (module-path-index-join where #f))])
    (parameterize ([current-namespace (make-empty-namespace)])
      (namespace-attach-module (current-namespace) ''#%kernel)
      (parameterize ([current-module-declare-name name])
        (eval `(,#'module any '#%kernel
                 (#%provide ,what)
                 (define-values (,what) #f))))
      (namespace-require `(for-template ,name))
      (namespace-syntax-introduce (datum->syntax #f what)))))
