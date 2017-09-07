#lang typed/racket/base

(provide prims-13@)

(require racket/match
         racket/set
         racket/contract
         typed/racket/unit
         "def.rkt"
         "signatures.rkt")

(define-unit prims-13@
  (import prim-runtime^)
  (export)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;; 13.1 Ports
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  ;; 13.1.2 Managing Ports
  (def input-port? (any/c . -> . boolean?))
  (def output-port? (any/c . -> . boolean?))
  (def port? (any/c . -> . boolean?))
  (def close-input-port (input-port? . -> . void?) #:lift-concrete? #f)
  (def close-output-port (output-port? . -> . void?) #:lift-concrete? #f)
  (def current-input-port  (-> input-port?) #:volatile? #t #:lift-concrete? #f)
  (def current-output-port (-> output-port?) #:volatile? #t #:lift-concrete? #f)
  (def current-error-port (-> output-port?) #:volatile? #t #:lift-concrete? #f)
  (def-const eof)
  (def eof-object? (any/c . -> . boolean?))

  ;; 13.1.3 Port Buffers and Positions
  (def flush-output (-> void?) #:lift-concrete? #f) ; FIXME uses

  ;; 13.1.5 File Ports
  (def open-input-file (path-string? . -> . input-port?) #:volatile? #t #:lift-concrete? #f)
  (def open-output-file (path-string? . -> . output-port?) #:volatile? #t #:lift-concrete? #f)
  (def call-with-input-file (∀/c (α) (path-string? (input-port? . -> . α) . -> . α)))
  (def call-with-output-file (∀/c (α) (path-string? (output-port? . -> . α) . -> . α)))
  (def with-input-from-file (∀/c (α) (path-string? (-> α) . -> . α)))
  (def with-output-to-file (∀/c (α) (path-string? (-> α) . -> . α)))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;; 13.2 Byte and String Input
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
  (def read-char
    (case->
     [-> (or/c char? eof-object?)]
     [input-port? . -> . (or/c char? eof-object?)])
    #:volatile? #t #:lift-concrete? #f)
  (def peek-char
    (case->
     [-> (or/c char? eof-object?)]
     [input-port? . -> . (or/c char? eof-object?)])
    #:volatile? #t #:lift-concrete? #f)


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;; 13.3 Byte and String Output
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
  (def write-char
    (case->
     [char? . -> . void?]
     [char? output-port? . -> . void?])
    #:lift-concrete? #f)
  (def newline
    (case->
     [-> void?]
     [output-port? . -> . void?])
    #:lift-concrete? #f)


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;; 13.4 Reading
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (def read
    (case->
     [-> any/c]
     [input-port? . -> . any/c])
    #:volatile? #t #:lift-concrete? #f)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;; 13.5 Writing
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
  (def write
    (case->
     [any/c . -> . void?]
     [any/c output-port? . -> . void?])
    #:lift-concrete? #f)
  (def display
    (case->
     [any/c . -> . void?]
     [any/c output-port? . -> . void?])
    #:lift-concrete? #f)
  (def displayln
    (case->
     [any/c . -> . void?]
     (any/c output-port? . -> . void?))
    #:lift-concrete? #f)
  (def fprintf (->* (output-port? string?) #:rest list? void?) #:lift-concrete? #f)
  (def printf (->* (string?) #:rest list? void?) #:lift-concrete? #f)
  (def format ((string?) #:rest list? . ->* . string?))
  )

