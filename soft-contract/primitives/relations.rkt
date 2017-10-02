#lang typed/racket/base

(provide relations@)


(require typed/racket/unit
         racket/string
         "def.rkt"
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
   [non-empty-string? ⇒ string?]
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
   [set-empty? ⇒ set?]
   [set? ⇒ generic-set?]
   ;; hash
   [hash-empty? ⇒ hash?]
   [hash-eq? ⇒ hash?]
   [hash-eqv? ⇒ hash?]
   [hash-equal? ⇒ hash?]
   [hash-weak? ⇒ hash?]
   ;; arity
   [normalized-arity? ⇒ procedure-arity?]
   [exact-nonnegative-integer? ⇒ normalized-arity?]
   [arity-at-least? ⇒ normalized-arity?]
   ;; contracts
   [char? ⇒ flat-contract?]
   [keyword? ⇒ flat-contract]
   [void? ⇒ flat-contract?]
   [number? ⇒ flat-contract?]
   [boolean? ⇒ flat-contract?]
   [symbol? ⇒ flat-contract?]
   [string? ⇒ flat-contract?]
   [null? ⇒ flat-contract?]
   [list-contract? ⇒ contract?]
   [flat-contract? ⇒ contract?]
   ;; ports
   [input-port? ⇒ port?]
   [output-port? ⇒ port?]
   ;; exceptions
   [exn:fail? ⇒ exn?]
   ;; procedures
   [primitive? ⇒ procedure?]
   )

  (dec-exclusions
   [exact-nonnegative-integer? negative?]
   [number? string? boolean? keyword? symbol? void? char? eof-object? null? procedure?
            vector? port? regexp? pregexp? byte-regexp? byte-pregexp? generic-set? hash? exn?]
   [positive? negative? zero?])

  (dec-partitions
   [number? {exact? inexact?}]))
