#lang typed/racket/base

;; This module provides type bindings for restricted use-cases of contract combinators

(require/typed/provide racket/contract
  [=/c  (Real → Any → Boolean)]
  [</c (Real → Any → Boolean)]
  [>/c (Real → Any → Boolean)]
  [>=/c (Real → Any → Boolean)]
  [<=/c (Real → Any → Boolean)]
  [between/c (Real Real → Any → Boolean)]
  ;[or/c ([] #:rest (Any → Any) . ->* . (Any → Any))]
  ;[and/c ([] #:rest (Any → Any) . ->* . (Any → Any))]
  ;[not/c ((Any → Any) → Any → Boolean)]
  [any/c (Any → #t)]
  [none/c (Any → #f)])
