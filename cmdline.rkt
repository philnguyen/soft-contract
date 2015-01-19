#lang typed/racket/base

(require "expand.rkt" racket/cmdline racket/list racket/pretty
         "lang.rkt"
         (only-in "check.rkt" feedback))
(require/typed "parse.rkt"
  [files->prog ((Listof Path-String) → .prog)])

(define fnames
  (cast (command-line #:program "raco soft-contract"
                        #:args (fname . fnames)
                        (cons fname fnames))
          (Listof Path-String)))

#;(define expanded-stx (do-expand-file fname))


#;(define (submodules-of expanded-stx)
  (syntax-case expanded-stx (module configure-runtime)
    [(module _name _lang
       (#%module-begin
        (module configure-runtime '#%kernel _ ...)
        (module name lang body ...) ...))
     (syntax->list #'((module name lang body ...) ...))]))



#;(require racket/pretty)
#;(printf "~a~n" prog)

(define prog (files->prog fnames))
(feedback prog)

;; FIXME
#;(define (find/havoc-provides submod) null)

#;(define havoc-provides (append-map find/havoc-provides (submodules-of expanded-stx)))

#;(feedback (map syntax->datum (append (submodules-of expanded-stx) havoc-provides)))
