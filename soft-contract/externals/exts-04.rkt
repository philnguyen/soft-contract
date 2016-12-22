#lang typed/racket/base

(require racket/contract
         "def-ext.rkt")

(def-ext for-each (procedure? list? . -> . void?))
