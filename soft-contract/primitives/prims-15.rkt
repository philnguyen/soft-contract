#lang typed/racket/base

(provide prims-15@)

(require racket/contract
         typed/racket/unit
         "def-prim.rkt"
         "../signatures.rkt"
         "signatures.rkt")

(define-unit prims-15@
  (import prim-runtime^ proof-system^ widening^)
  (export)

  
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

  ;; 15.2.6 More File and Directory Utilities
  (def-prim file->list (path-string? . -> . list?) #:volatile? #t #:lift-concrete? #f)


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;; 15.7
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  {def-prim getenv (string? . -> . (or/c string? not)) #:lift-concrete? #f}
  {def-prim putenv (string? string? . -> . boolean?) #:lift-concrete? #f}
  )

