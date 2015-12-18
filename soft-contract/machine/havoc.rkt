#lang typed/racket/base

(provide gen-havoc -havoc-id -havoc-src)

(require
 racket/match racket/set
 "../utils/pretty.rkt" "../utils/set.rkt" "../utils/map.rkt"
 "../ast/definition.rkt"
 "../runtime/val.rkt" "../runtime/env.rkt" "../runtime/path-inv.rkt" "../runtime/addr.rkt")

(define -havoc-path 'havoc)
(define -havoc-id (-id 'havoc-id -havoc-path)) ; havoc function id
(define -havoc-src (-src-loc -havoc-path (next-neg!))) ; havoc module path

(define (havoc-ref-from [ctx : Mon-Party] [pos : Integer])
  (-ref -havoc-id ctx pos))

(: prog-accs : (Listof -module) → (Setof -st-ac))
;; Retrieve set of all public accessors from program
(define (prog-accs ms)
  (define-values (defs decs)
    (for*/fold ([defs : (HashTable Symbol -st-ac) (hash)]
                [decs : (Setof Symbol) {set}])
               ([m ms]
                [form (-plain-module-begin-body (-module-body m))])
      (match form
        [(-provide _ specs)
         (define decs*
           (for/fold ([decs : (Setof Symbol) decs])
                     ([spec specs])
             (set-add decs (-p/c-item-id spec))))
         (values defs decs*)]
        [(-define-values _ (list id) e)
         (define defs*
           (match e
             [(? -st-ac? ac) (hash-set defs id ac)]
             [_ defs]))
         (values defs* decs)]
        [_ (values defs decs)])))
  (for/set: : (Setof -st-ac) ([(id ac) (in-hash defs)] #:when (∋ decs id))
    ac))

(: gen-havoc : (Listof -module) → (Values -Clo -e))
;; Allocate `havoc` in `σ` and return `e` that havocs each value
(define (gen-havoc ms)

  ;; Generate value
  (define x (-x '☠))
  (define acs-for-struct
    (for/fold ([m : (HashTable -struct-info (Setof -st-ac)) (hash)])
              ([ac (prog-accs ms)])
      (match-define (-st-ac si _) ac)
      (hash-update m si (λ ([acs : (Setof -st-ac)]) (set-add acs ac)) (λ () {set ac}))))
  (define alts
    (cons
     (cons (-@ 'procedure? (list x) -havoc-src)
           (-@ (havoc-ref-from -havoc-path (next-neg!))
                     (list (-@-havoc x)) -havoc-src))
     (for/list : (Listof (Pairof -e -e)) ([(si acs) acs-for-struct])
       (cons (-@ (-st-p si) (list x) -havoc-src)
             (-amb/simp
              (for/list : (Listof -@) ([ac acs])
                (-@ (havoc-ref-from -havoc-path (next-neg!))
                    (list (-@ ac (list x) -havoc-src))
                    -havoc-src)))))))
  (define havoc-body (-cond alts (-amb ∅)))
  (define clo-havoc ; only used by `verify` module, not `ce`
    (-Clo '(☠) havoc-body -ρ⊥ -Γ⊤))

  ;; Generate havoc-ing expression
  (define-set refs : -ref)
  ;(log-debug "~nmodules: ~n~a~n" ms)
  (for ([m (in-list ms)])
    (cond
      [(module-opaque? m)
       =>
       (λ (s)
         (log-debug "Omit havocking opaque module `~a`. Provided but undefined: ~a~n"
                   (-module-path m)
                   (set->list s)))]
     [else
      #;(log-debug "Havocking transparent module ~a~n" (-module-path m))
      (match-define (-module path (-plain-module-begin forms)) m)
      #;(eprintf "Insert exported identifiers from module ~a to unknown contexts~n" path)
      (for* ([form (in-list forms)] #:when (-provide? form)
             [spec (in-list (-provide-specs form))])
        (log-debug "adding: ~a~n" (-p/c-item-id spec))
        (refs-add! (-ref (-id (-p/c-item-id spec) path) '† (next-neg!))))]))
  ;(log-debug "~nrefs: ~a~n" refs)
  (define expr
    (-amb/remember (for/list ([ref (in-set refs)])
                     (-@ (•!) (list ref) -havoc-src))))

  ;(log-debug "~nhavoc-e:~n~a" expr)

  (values clo-havoc expr))

(: module-opaque? : -module → (U #f (Setof Symbol)))
;; Check whether module is opaque, returning the set of opaque exports if so
(define (module-opaque? m)
  (match-define (-module p (-plain-module-begin body)) m)
  (case p
    [(Λ † havoc) #|HACK|# ∅]
    [else
     (define-values (exports defines)
       (for/fold ([exports : (Setof Symbol) ∅] [defines : (Setof Symbol) ∅])
                 ([e (in-list body)])
         (match e
           [(-provide _ specs)
            (values (set-add-list exports (map -p/c-item-id specs)) defines)]
           [(-define-values _ xs _)
            (values exports (set-add-list defines xs))]
           [_ (values exports defines)])))

     (if (⊆ exports defines) #f (-- exports defines))]))
