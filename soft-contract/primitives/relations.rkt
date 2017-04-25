#lang typed/racket/base

;; TODO: not that nice. This module needs to be required for the side effects

(require "def-prim.rkt")

(dec-implications
 ;; numbers
 [zero? ⇒ byte?]
 [byte? ⇒ fixnum?]
 [fixnum? ⇒ integer?]
 [integer? ⇒ rational?]
 [real? ⇒ number?]
 [float-complex? ⇒ number?]
 [not ⇒ boolean?]
 [exact-integer? ⇒ integer?]
 [exact-integer? ⇒ exact?]
 [exact-nonnegative-integer? ⇒ exact-integer?]
 [exact-positive-integer? ⇒ positive?]
 [exact-positive-integer? ⇒ exact-nonnegative-integer?]
 [inexact-real? ⇒ real?]
 [rational? ⇒ real?]
 [flonum? ⇒ inexact-real?]
 [single-flonum? ⇒ flonum?]
 [double-flonum? ⇒ flonum?]
 ;; strings
 [path-string? ⇒ string?]
 [string? ⇒ path-string?] ; TODO tmp. cheat
 ;; sequence
 [exact-nonnegative-integer? ⇒ sequence?]
 [string? ⇒ sequence?]
 [bytes ⇒ sequence?]
 [list? ⇒ sequence?]
 [vector? ⇒ sequence?]
 [flvector? ⇒ sequence?]
 [fxvector? ⇒ sequence?]
 [hash? ⇒ sequence?]
 [dict? ⇒ sequence?]
 [set? ⇒ sequence?]
 [input-port? ⇒ sequence?]
 [stream? ⇒ sequence?]
 ;; sets
 [set-equal? ⇒ set?]
 [set-eqv? ⇒ set?]
 [set-eq? ⇒ set?]
 [set-mutable? ⇒ set?]
 [set-weak? ⇒ set?]
 ;; arity
 [exact-nonnegative-integer? ⇒ procedure-arity?]
 ;; contracts
 [flat-contract? ⇒ contract?]
 ;; ports
 [input-port? ⇒ port?]
 [output-port? ⇒ port?]
 )

(dec-exclusions
 [exact-nonnegative-integer? negative?]
 [number? string? boolean? keyword? symbol? void? char? eof-object? null? procedure? vector? port? regexp? pregexp? byte-regexp? byte-pregexp?])

(dec-partitions
 [number? {exact? inexact?}])
