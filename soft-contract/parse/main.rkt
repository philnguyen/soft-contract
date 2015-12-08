#lang typed/racket/base

(require "../ast/definition.rkt")
(require/typed/provide "private.rkt"
  [files->modules ((Listof Path-String) → (Listof -module))]
  [init-prim (Listof -module-level-form)])
