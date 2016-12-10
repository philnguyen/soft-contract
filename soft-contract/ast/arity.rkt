#lang typed/racket/base

(provide Arity arity-includes? normalize-arity)

(require "../utils/def.rkt")
(require/typed racket/function
  [arity-includes? (Arity Arity → Boolean)]
  [normalize-arity ((Listof Arity) → Arity)])

;; The kind of arities that we care about, for now
(Arity . ::= . Natural arity-at-least (Listof (U Natural arity-at-least)))
