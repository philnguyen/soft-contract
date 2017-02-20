#lang typed/racket/base

(require racket/match "../ast/main.rkt")
(require/typed "private.rkt"
  [(file->module file->module*) (Path-String → -module)])

(provide file->module)

(: file->module : Path-String → -module)
;; Alpha renaming on top of the old parser (hack)
(define (file->module p)
  (define m (α-rename (file->module* p)))
  (collect-public-accs! m)
  m)


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;; Collect other information
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(: collect-public-accs! : -module → Void)
;; Retrieve set of all public accessors from program, grouped by struct
(define (collect-public-accs! m)
  
  ;; Collect all defined accessors (`defs`) and exported identifiers (`decs`)
  (define acc-defs : (HashTable Symbol -st-ac ) (make-hasheq))
  (define mut-defs : (HashTable Symbol -st-mut) (make-hasheq))
  (define decs     : (HashTable Symbol #t     ) (make-hasheq))
  (for ([form (in-list (-module-body m))])
    (match form
      [(-provide specs)
       (for ([spec (in-list specs)])
         (match-define (-p/c-item x _ _) spec)
         (hash-set! decs x #t))]
      [(-define-values (list x) (? -st-ac? e))
       (hash-set! acc-defs x e)]
      [(-define-values (list x) (? -st-mut? e))
       (hash-set! mut-defs x e)]
      [_ (void)]))
  
  ;; Collect exported accessors and mutators
  (for ([(x ac) (in-hash acc-defs)] #:when (hash-has-key? decs x))
    (match-define (-st-ac 𝒾 _) ac)
    (add-public-acc! 𝒾 ac))
  (for ([(x mut) (in-hash mut-defs)] #:when (hash-has-key? decs x))
    (match-define (-st-mut 𝒾 _) mut)
    (add-public-mut! 𝒾 mut)))
