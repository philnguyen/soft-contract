#lang typed/racket/base

(require racket/match "../ast/main.rkt")
(require/typed "private.rkt"
  [(parse-files parse-files*) ((Listof Path-String) → (Listof -module))])

(provide parse-files)

(: parse-files : (Listof Path-String) → (Listof -module))
;; Alpha renaming on top of the old parser (hack)
(define (parse-files ps)
  (define ms (map α-rename (parse-files* ps)))
  (for ([m (in-list ms)])
    (collect-public-accs! m))
  ms)


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
