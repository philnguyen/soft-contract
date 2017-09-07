#lang typed/racket/base

(require racket/match
         racket/contract
         racket/bool
         racket/string
         racket/math
         racket/list
         racket/stream
         racket/dict
         racket/function
         racket/set
         racket/flonum
         racket/fixnum
         racket/generator
         racket/random
         racket/format
         racket/splicing
         typed/racket/unit
         syntax/parse/define
         set-extras
         "../utils/debug.rkt"
         (except-in "../ast/signatures.rkt" normalize-arity arity-includes?)
         "signatures.rkt"
         "def.rkt"
         (for-syntax racket/base
                     racket/syntax
                     syntax/parse))

(provide prims-04-07@)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;; 4.7 Regular Expressions
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define-unit prims-04-07@
  (import prim-runtime^)
  (export)

  ;; 4.7.3 Constructors
  (def-pred regexp?)
  (def-pred pregexp?)
  (def-pred byte-regexp?)
  (def-pred byte-pregexp?)
  (def regexp (string? . -> . regexp?))
  (def pregexp (string? . -> . pregexp?))
  (def byte-regexp (bytes? . -> . regexp?))
  (def byte-pregexp (bytes? . -> . pregexp?))
  (def regexp-quote ; FIXME uses
    ((or/c string? bytes?) . -> . (or/c string? bytes?))
    #:refinements
    (string? . -> . string?)
    (bytes? . -> . bytes?))
  (def regexp-max-lookbehind
    ((or/c regexp? byte-regexp?) . -> . exact-nonnegative-integer?))

  ;; 4.7.4 Regexp Matching
  (def regexp-match ; FIXME uses, precision
    ((or/c string? bytes? regexp? byte-regexp?)
     (or/c string? bytes? path? input-port?)
     . -> .
     any/c))
  (def regexp-match* ; FIXME uses, precision
    ((or/c string? bytes? regexp? byte-regexp?)
     (or/c string? bytes? path? input-port?)
     . -> .
     any/c))
  (def regexp-try-match ; FIXME uses, precision
    ((or/c string? bytes? regexp? byte-regexp?)
     (or/c string? bytes? path? input-port?)
     . -> .
     any/c))
  (def regexp-match-positions ; FIXME uses, precision
    ((or/c string? bytes? regexp? byte-regexp?)
     (or/c string? bytes? path? input-port?)
     . -> .
     any/c))
  (def regexp-match-positions* ; FIXME uses, precision
    ((or/c string? bytes? regexp? byte-regexp?)
     (or/c string? bytes? path? input-port?)
     . -> .
     any/c))
  (def regexp-match? ; FIXME uses
    ((or/c string? bytes? regexp? byte-regexp?)
     (or/c string? bytes? path? input-port?)
     . -> .
     boolean?))
  (def regexp-match-exact? ; FIXME uses
    ((or/c string? bytes? regexp? byte-regexp?)
     (or/c string? bytes? path?)
     . -> .
     boolean?))
  (def regexp-match-peek ; FIXME uses ; FIXME listof
    ((or/c string? bytes? regexp? byte-regexp?)
     input-port?
     . -> .
     (or/c pair? #;(cons/c bytes? (listof (or/c bytes? not)))
           not)))
  (def regexp-match-peek-positions ; FIXME uses ; FIXME listof
    ((or/c string? bytes? regexp? byte-regexp?)
     input-port?
     . -> .
     (or/c pair? #;(cons/c (cons/c exact-nonnegative-integer?
                                   exact-nonnegative-integer?)
                           (listof (or/c (cons/c exact-nonnegative-integer?
                                                 exact-nonnegative-integer?)
                                         not)))
           not)))
  (def regexp-match-peek-immediate ; FIXME uses ; FIXME listof
    ((or/c string? bytes? regexp? byte-regexp?)
     input-port?
     . -> .
     (or/c pair? #;(cons/c bytes? (listof (or/c bytes? not)))
           not)))
  (def regexp-match-peek-positions-immediate ; FIXME uses ; FIXME listof
    ((or/c string? bytes? regexp? byte-regexp?)
     input-port?
     . -> .
     (or/c pair? #;(cons/c (cons/c exact-nonnegative-integer?
                                   exact-nonnegative-integer?)
                           (listof (or/c (cons/c exact-nonnegative-integer?
                                                 exact-nonnegative-integer?)
                                         not)))
           not)))
  (def regexp-match-peek-positions* ; FIXME uses, precision ; FIXME listof
    ((or/c string? bytes? regexp? byte-regexp?)
     input-port?
     . -> .
     list? #;(or/c (listof (cons/c exact-nonnegative-integer?
                                   exact-nonnegative-integer?))
                   (listof (listof (or/c not (cons/c exact-nonnegative-integer?
                                                     exact-nonnegative-integer?)))))))
  (def regexp-match/end
    ((or/c string? bytes? regexp? byte-regexp?)
     (or/c string? bytes? path? input-port?)
     . -> .
     any/c))
  (def regexp-match-positions/end ; FIXME uses
    ((or/c string? bytes? regexp? byte-regexp?)
     (or/c string? bytes? path? input-port?)
     . -> .
     any/c))
  (def regexp-match-peek-positions/end
    ((or/c string? bytes? regexp? byte-regexp?)
     input-port?
     . -> .
     any/c))
  (def regexp-match-peek-positions-immediate/end
    ((or/c string? bytes? regexp? byte-regexp?)
     input-port?
     . -> .
     any/c))

  ;; 4.7.5 Regexp Splitting
  (def regexp-split ; FIXME uses, precision
    ((or/c string? bytes? regexp? byte-regexp?)
     (or/c string? bytes? input-port?)
     . -> .
     any/c))

  ;; 4.7.6 Regexp Substitution
  (def regexp-replace ; FIXME uses, precision
    ((or/c string? bytes? regexp? byte-regexp?)
     (or/c string? bytes?)
     (or/c string? bytes? #|TODO more|#)
     . -> .
     any/c))
  (def regexp-replace* ; FIXME uses
    ((or/c string? bytes? regexp? byte-regexp?)
     (or/c string? bytes?)
     (or/c string? bytes? #|TODO more|#)
     . -> .
     (or/c string? bytes?)))
  (def regexp-replaces ; FIXME listof
    ((or/c string? bytes?)
     (listof
      list? #;(list/c (or/c string? bytes regexp? byte-regexp?)
                      (or/c string bytes? #|TODO more|#)))
     . -> .
     (or/c string? bytes?)))
  (def regexp-replace-quote
    ((or/c string? bytes?) . -> . (or/c string? bytes?))
    #:refinements
    (string? . -> . string?)
    (bytes? . -> . bytes?))
  
  )
