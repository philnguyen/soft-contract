#lang typed/racket/base

(provide (all-defined-out))

(require racket/contract
         "def-prim.rkt")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;; 13.1 Ports
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; 13.1.2 Managing Ports
(def-prim input-port? (any/c . -> . boolean?))
(def-prim output-port? (any/c . -> . boolean?))
(def-prim port? (any/c . -> . boolean?))
(def-prim eof-object? (any/c . -> . boolean?))
(def-prim current-input-port  (-> input-port?) #:lift-concrete? #f)
(def-prim current-output-port (-> output-port?) #:lift-concrete? #f)
(def-prim current-error-port (-> output-port?) #:lift-concrete? #f)

;; 13.1.3 Port Buffers and Positions
(def-prim flush-output (-> void?) #:lift-concrete? #f) ; FIXME uses

;; 13.1.5 File Ports
; [HO] call-with-input-file call-with-output-file


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;; 13.2 Byte and String Input
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
(def-prim read-char (input-port? . -> . (or/c char? eof-object?)) #:lift-concrete? #f) ; FIXME uses
(def-prim peek-char (input-port? . -> . (or/c char? eof-object?)) #:lift-concrete? #f) ; FIXME uses

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;; 13.3 Byte and String Output
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
(def-prim write-char (char? output-port? . -> . void?) #:lift-concrete? #f) ; FIXME uses
(def-prim newline (output-port? . -> . void?) #:lift-concrete? #f) ; FIXME uses


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;; 13.5 Writing
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
(def-prim write (any/c output-port? . -> . void?) #:lift-concrete? #f) ; FIXME uses
(def-prim display (any/c output-port? . -> . void?) #:lift-concrete? #f) ; FIXME uses
