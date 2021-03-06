#lang typed/racket/base

(provide (all-defined-out))

(require typed/racket/unit
         "../ast/signatures.rkt")

(define-signature parser-helper^
  ([parse-files : ((Listof Path-String) → (Listof -module))]
   [parse-stxs : ((Listof Path-String) (Listof Syntax) → (Listof -module))]
   [parse-module : (Syntax → -module)]
   [parse-e : (Syntax → -e)]
   [canonicalize-path : (Path-String → Path-String)]))

(struct exn:missing exn:fail ([path : Path-String] [id : Symbol]) #:transparent)
