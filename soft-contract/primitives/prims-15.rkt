#lang typed/racket/base

(provide (all-defined-out))

(require racket/contract
         "def-prim.rkt")


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;; 15.1 Paths
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; 15.1.1 Manipulating Paths
(def-pred path-string?)


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;; 15.2 Filesystem
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; 15.2.2 Files
(def-prim file-exists? (path-string? . -> . boolean?) #:lift-concrete? #f)
(def-prim delete-file (path-string? . -> . void?) #:lift-concrete? #f)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;; 15.7
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

{def-prim getenv (string? . -> . (or/c string? not)) #:lift-concrete? #f}
{def-prim putenv (string? string? . -> . boolean?) #:lift-concrete? #f}

