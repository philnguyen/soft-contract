#lang typed/racket/base

(require racket/match
         racket/splicing
         typed/racket/unit
         "../ast/signatures.rkt"
         "../signatures.rkt"
         "signatures.rkt"
         "private.rkt")

(provide parser@)

(define-unit pre-parser@
  (import static-info^ prims^ (prefix pre: parser-helper^))
  (export parser^)

  (splicing-local
      ((: with-post-processing : (Listof -module) → (Listof -module))
       ;; Alpha renaming on top of the old parser (hack)
       (define (with-post-processing ms)
         (for-each collect-public-accs! ms)
         (for-each collect-transparent-modules! ms)
         ms))
    (: parse-files : (Listof Path-String) → (Listof -module))

    (define (parse-files ps)
      (with-post-processing (pre:parse-files (map pre:canonicalize-path ps))))

    (: parse-stxs : (Listof Path-String) (Listof Syntax) → (Listof -module))
    (define (parse-stxs fns stxs)
      (with-post-processing (pre:parse-stxs fns stxs))))

  (: parse-module : Syntax → -module)
  (define (parse-module stx)
    (define m (pre:parse-module stx))
    (collect-public-accs! m)
    m)

  (: parse-expr : Syntax → -e)
  (define parse-expr pre:parse-e)


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
           (match spec
             [(-p/c-item x _ _)
              (hash-set! decs x #t)]
             [(? symbol? x) (hash-set! decs x #t)]))]
        [(-define-values (list x) (? -st-ac? e) _)
         (hash-set! acc-defs x e)]
        [(-define-values (list x) (? -st-mut? e) _)
         (hash-set! mut-defs x e)]
        [_ (void)]))
    
    ;; Collect exported accessors and mutators
    (for ([(x ac) (in-hash acc-defs)] #:when (hash-has-key? decs x))
      (match-define (-st-ac 𝒾 _) ac)
      (add-public-acc! 𝒾 ac))
    (for ([(x mut) (in-hash mut-defs)] #:when (hash-has-key? decs x))
      (match-define (-st-mut 𝒾 _) mut)
      (add-public-mut! 𝒾 mut)))

  (define collect-transparent-modules! : (-module → Void)
    (match-lambda
      [(-module l body)
       (add-transparent-module! l)
       (for ([form (in-list body)] #:when (-module? form))
         (collect-transparent-modules! form))]))

  (define canonicalize-path pre:canonicalize-path)
  )

(define-compound-unit/infer parser@
  (import static-info^ meta-functions^ ast-macros^ prims^)
  (export parser^)
  (link parser-helper@ pre-parser@))

