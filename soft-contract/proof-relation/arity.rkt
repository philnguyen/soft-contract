#lang typed/racket/base

(provide V-arity formals-arity guard-arity)

(require racket/match
         racket/list
         "../utils/list.rkt"
         "../ast/main.rkt"
         "definition.rkt")

