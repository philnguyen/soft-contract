#lang typed/racket/base

(require "expand.rkt" racket/cmdline racket/list racket/pretty
         "ast.rkt"
         (only-in "check.rkt" analyze))
(require/typed "parse.rkt"
  [files->prog ((Listof Path-String) → -prog)])

(define fname
  (cast (command-line #:program "raco soft-contract"
                      #:args (fname) ; TODO re-enable file list
                      fname)
        Path-String))

(analyze fname)

;; FIXME
#;(define (find/havoc-provides submod) null)

#;(define havoc-provides (append-map find/havoc-provides (submodules-of expanded-stx)))

#;(feedback (map syntax->datum (append (submodules-of expanded-stx) havoc-provides)))
