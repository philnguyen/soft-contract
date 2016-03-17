#lang typed/racket/base

(require racket/match "../ast/main.rkt")
(require/typed "private.rkt"
  [(files->modules files->modules*) ((Listof Path-String) → (Listof -module))])

(provide files->modules)

(: files->modules : (Listof Path-String) → (Listof -module))
;; Alpha renaming on top of the old parser (hack)
(define (files->modules paths)
  (map rename-module (files->modules* paths)))

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
        (match-define (-p/c-item x c) spec)
        (-p/c-item x (α-rename c))))]
    [(? -require? d) d]
    [(? -e? e) (α-rename e)]))
