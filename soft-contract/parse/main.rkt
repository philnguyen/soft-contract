#lang typed/racket/base

(require racket/match "../ast/main.rkt")
(require/typed "private.rkt"
  [(file->module file->module*) (Path-String → -module)])

(provide file->module)

(: file->module : Path-String → -module)
;; Alpha renaming on top of the old parser (hack)
(define (file->module p)
  (rename-module (file->module* p)))

(: rename-module : -module → -module)
(define (rename-module m)
  (match-define (-module p forms) m)
  (-module p (map rename-module-level-form forms)))

(: rename-module-level-form : -module-level-form → -module-level-form)
(define rename-module-level-form
  (match-lambda
    [(-define-values xs e) (-define-values xs (α-rename e))]
    [(-provide specs)
     (-provide
      (for/list ([spec specs])
        (match-define (-p/c-item x c ℓ) spec)
        (-p/c-item x (α-rename c) ℓ)))]
    [(? -require? d) d]
    [(? -e? e) (α-rename e)]))
