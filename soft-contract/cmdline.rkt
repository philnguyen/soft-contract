#lang typed/racket/base

(require
 racket/cmdline racket/list racket/pretty
 (only-in "check.rkt" analyze))

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
