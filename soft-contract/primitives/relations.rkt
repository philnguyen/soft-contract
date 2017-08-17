#lang typed/racket/base

(provide relations@)


(require typed/racket/unit
         "def-prim.rkt"
         "signatures.rkt")

(define-unit relations@
  (import prim-runtime^)
  (export)
  
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
   [set? ⇒ generic-set?]
   ;; arity
   [exact-nonnegative-integer? ⇒ procedure-arity?]
   ;; contracts
   [flat-contract? ⇒ contract?]
   ;; ports
   [input-port? ⇒ port?]
   [output-port? ⇒ port?]
   ;; exceptions
   [exn:fail? ⇒ exn?]
   )

  (dec-exclusions
   [exact-nonnegative-integer? negative?]
   [number? string? boolean? keyword? symbol? void? char? eof-object? null? procedure?
            vector? port? regexp? pregexp? byte-regexp? byte-pregexp? generic-set? hash? exn?]
   [positive? negative? zero?])

  (dec-partitions
   [number? {exact? inexact?}]))
