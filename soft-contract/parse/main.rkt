#lang typed/racket/base

(require racket/match "../ast/main.rkt")
(require/typed "private.rkt"
  [(file->module file->module*) (Path-String → -module)])

(provide file->module)

(: file->module : Path-String → -module)
;; Alpha renaming on top of the old parser (hack)
(define (file->module p) (α-rename (file->module* p)))
