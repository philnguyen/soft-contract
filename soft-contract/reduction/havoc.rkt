#lang typed/racket/base

(provide gen-havoc-Clo gen-havoc-exp havoc-id)

(require
 racket/match racket/set
 "../utils/set.rkt"
 "../ast/definition.rkt"
 "../runtime/main.rkt"
 "step.rkt")

(define havoc-path 'havoc)
(define havoc-id (-id 'havoc-id havoc-path))
(define havoc-src (-src-loc havoc-path (next-loc!)))

(: prog-accs : (Listof -module) → (℘ -st-ac))
;; Retrieve set of all public accessors from program
(define (prog-accs ms)
  
  ;; Collect all defined accessors (`defs`) and exported identifiers (`decs`)
  (define defs : (HashTable Symbol -st-ac) (make-hasheq))
  (define decs : (HashTable Symbol #t    ) (make-hasheq))
  (for* ([m ms]
         [form (-module-body m)])
    (match form
      [(-provide _ specs)
       (for-each
        (match-lambda [(-p/c-item x _) (hash-set! decs x #t)])
        specs)]
      [(-define-values _ (list x) (? -st-ac? e))
       (hash-set! defs x e)]
      [_ (void)]))
  
  ;; Return exported accessors
  (for/set: : (℘ -st-ac) ([(x ac) (in-hash defs)] #:when (hash-has-key? decs x))
    ac))

(: gen-havoc-Clo : (Listof -module) → -Clo)
;; Generate the unknown context
;; Only used by `verify` module, not `ce`
(define (gen-havoc-Clo ms)

  (define (havoc-ref-from [ctx : Mon-Party] [pos : Integer])
    (-ref havoc-id ctx pos))

  (define x (-x '☠))

  (define acs-for-struct
    (for/fold ([m : (HashTable -struct-info (℘ -st-ac)) (hash)])
              ([ac (prog-accs ms)])
      (match-define (-st-ac si _) ac)
      (hash-update m si (λ ([acs : (℘ -st-ac)]) (set-add acs ac))
                        (λ () {set ac}))))
  
  (define alts
    (cons
     (cons (-@ 'procedure? (list x) havoc-src)
           (-@ (havoc-ref-from havoc-path (next-loc!))
               (list (-@-havoc x)) havoc-src))
     (for/list : (Listof (Pairof -e -e)) ([(si acs) acs-for-struct])
       (cons (-@ (-st-p si) (list x) havoc-src)
             (-amb/simp
              (for/list : (Listof -@) ([ac acs])
                (-@ (havoc-ref-from havoc-path (next-loc!))
                    (list (-@ ac (list x) havoc-src))
                    havoc-src)))))))
  
  (define havoc-body (-cond alts (-amb ∅)))
  
  (-Clo '(☠) (⇓ havoc-body) ⊥ρ ⊤Γ))

(: gen-havoc-exp : (Listof -module) → -e)
;; Generate havoc top-level expression havoc-king modules' exports
(define (gen-havoc-exp ms)
  (define-set refs : -ref)
  
  (for ([m (in-list ms)])
    (match-define (-module path forms) m)
    (for* ([form forms] #:when (-provide? form)
           [spec (-provide-specs form)])
      (match-define (-p/c-item x _) spec)
      (refs-add! (-ref (-id x path) '† (next-loc!)))))
  
  (-amb/remember (for/list ([ref (in-set refs)])
                   (-@ (•!) (list ref) havoc-src))))

