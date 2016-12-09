#lang typed/racket/base

;; This module defines primitive operations on first-order data,
;; each of which is an atomic operation that can be perform in 1 "step",
;; returning a set of possible answers paired with path-conditions.
;; 
;; First-order "library functions" and "primitives", as far as this tool is concerned, are the same.
;; A higher-order function, however, can invoke behavioral values fed to it arbitrarily,
;; and must be approximated by `havoc`, thus is not an "atomic" operation
;; definable in this module.

(require "def-prim-runtime.rkt" "prims.rkt" "relations.rkt")
(provide (all-from-out "def-prim-runtime.rkt" "prims.rkt" "relations.rkt"))
