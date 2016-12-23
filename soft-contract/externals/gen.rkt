#lang typed/racket/base

(provide (for-syntax (all-defined-out))
         (all-from-out "../primitives/gen.rkt"))

(require (for-syntax racket/base
                     racket/match
                     racket/contract
                     racket/syntax
                     syntax/parse
                     "../primitives/utils.rkt")
         racket/match
         racket/contract
         "../utils/map.rkt"
         "../utils/set.rkt"
         "../ast/definition.rkt"
         "../runtime/main.rkt"
         "../primitives/gen.rkt"
         "def-ext-runtime.rkt")

(begin-for-syntax

  (define-parameter/contract
    [-$ identifier? #f]
    [-ℒ identifier? #f]
    [-⟦k⟧ identifier? #f]))
