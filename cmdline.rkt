#lang racket/base

(require "expand.rkt" racket/cmdline racket/list racket/pretty)

(define fname (command-line #:program "raco soft-contract"
               #:args (fname)
               fname))

(define expanded-stx (do-expand-file fname))

(define (submodules-of expanded-stx)
  (syntax-case expanded-stx (module configure-runtime)
    [(module _name _lang
       (#%module-begin
        (module configure-runtime '#%kernel _ ...)
        (module name lang body ...) ...))
     (syntax->list #'((module name lang body ...) ...))]))

(require racket/pretty)
(printf "~a~n" (pretty-print (map syntax->datum (submodules-of expanded-stx))))

;; FIXME
#;(define (find/havoc-provides submod) null)

#;(define havoc-provides (append-map find/havoc-provides (submodules-of expanded-stx)))

#;(feedback (map syntax->datum (append (submodules-of expanded-stx) havoc-provides)))
