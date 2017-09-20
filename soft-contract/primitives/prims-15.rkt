#lang typed/racket/base

(provide prims-15@)

(require racket/contract
         typed/racket/unit
         "def.rkt"
         "signatures.rkt")

(define-unit prims-15@
  (import prim-runtime^)
  (export)

  
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;; 15.1 Paths
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  ;; 15.1.1 Manipulating Paths
  (def-pred path-string?)
  (def string->path (string? . -> . path?))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;; 15.2 Filesystem
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;


  ;; 15.2.2 Files
  (def file-exists? (path-string? . -> . boolean?) #:lift-concrete? #f)
  (def delete-file (path-string? . -> . void?))

  ;; 15.2.6 More File and Directory Utilities
  (def file->list (path-string? . -> . list?))
  (def file->value (path-string? . -> . any/c))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;; 15.7
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (def getenv (string? . -> . (or/c string? not)) #:lift-concrete? #f)
  (def putenv (string? string? . -> . boolean?) #:lift-concrete? #f)
  )

