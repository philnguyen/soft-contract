#lang typed/racket/base

(provide Arity Arity? arity-includes? normalize-arity arity-0+)

(require bnf)
(require/typed racket/function
  [arity-includes? (Arity Arity → Boolean)]
  [normalize-arity ((Listof Arity) → Arity)])

;; The kind of arities that we care about, for now
(Arity . ::= . Natural
               arity-at-least
               [#:old (Listof (U Natural arity-at-least))])

(define arity-0+ (arity-at-least 0))
