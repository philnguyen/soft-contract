#lang typed/racket/base

(require racket/match racket/set "../utils/main.rkt")
(require/typed "declarations.rkt"
  [(implications prims:implications) (Listof Any)]
  [(prims prims:prims) (Listof Any)])

(provide Graph implications exclusions
         base-predicates prim-names prim-ranges prim-refinements-for-ranges
         ignore-for-now?)
(require/typed/provide "declarations.rkt"
  [base? (Sexp → Boolean)])

(define-type Graph (HashTable Symbol (℘ Symbol)))
(define -graph∅ : Graph (hasheq))

;; Compute a graph's reflexive-transitive closure
(define (refl-trans [m : Graph]) : Graph

  ;; Compute `m`'s reflexive closure
  (define m₀
    (let ([refl : (Graph Symbol → Graph)
           (λ (m k)
             (hash-update m k (λ ([vs : (℘ Symbol)]) (set-add vs k)) →∅eq))])
      (for*/fold ([m : Graph m])
                 ([(l rs) (in-hash m)]
                  [m (in-value (refl m l))]
                  [r (in-set rs)])
        (refl m r))))

  ;; Compute `m`'s transitive closure
  (fix
   (λ ([m : Graph])
     (for/hash : Graph ([(l rs) (in-hash m)])
       (define rs* (∪ rs (for/unioneq : (℘ Symbol) ([r rs]) (hash-ref m r))))
       (values l rs*)))
   m₀))

;; Add edge to graph
(define (add-edge [m : Graph] [l : Symbol] [r : Symbol]) : Graph
  (hash-update m l (λ ([rs : (℘ Symbol)]) (set-add rs r)) →∅eq))

;; Reverse a graph
(define (reverse-graph [m : Graph]) : Graph
  (for*/fold ([m : Graph -graph∅])
             ([(l rs) (in-hash m)] [r rs])
    (add-edge m r l)))

;; Compute conservative implications and exclusions
(define-values (implications exclusions)
  (let ()
    ;; Compute first versions of graphs to start with
    (define-values (im ex)
      (for/fold ([im : Graph -graph∅] [ex : Graph -graph∅])
                ([dec (in-list prims:implications)])
        (match dec
          [`(,(? symbol? l) ⇒ ,(? symbol? r))
           (values (add-edge im l r) ex)]
          [`(#:partition ,(? symbol? r) (,ls ...))
           (define im*
             (for/fold ([im : Graph im]) ([l ls])
               (add-edge im (assert l symbol?) r)))
           (define ex*
             (for*/fold ([ex : Graph ex]) ([l ls] [l* ls] #:unless (eq? l l*))
               (add-edge ex (assert l symbol?) (assert l* symbol?))))
           (values im* ex*)]
          [`(#:exclusion ,ss ...)
           (define im* ; to make sure `im` graph covers every key
             (for/fold ([im : Graph im]) ([s ss])
               (assert s symbol?)
               (add-edge im s s)))
           (define ex*
             (for*/fold ([ex : Graph ex]) ([s ss] [s* ss] #:unless (eq? s s*))
               (add-edge ex (assert s symbol?) (assert s* symbol?))))
           (values im* ex*)])))
    
    (define im* (refl-trans im))
    (define ex*
      (let ([im*⁻¹ (reverse-graph im*)])
        (fix
         (λ ([ex : Graph]) ; ⟦a ⇒ ¬b, c ⇒ b⟧ ⇒ a ⇒ ¬c
           (for*/fold ([ex : Graph ex])
                      ([(l rs) (in-hash ex)]
                       [r (in-set rs)]
                       [r* (in-set (hash-ref im*⁻¹ r))])
             (add-edge (add-edge ex l r*) r* l)))
         ex)))
    (values im* ex*)))

(define prim-names
  (for/fold ([names : (℘ Symbol) (seteq)])
            ([dec (in-list prims:prims)])
    (match dec
      [`(#:pred ,(? symbol? s) ,_ ...) (set-add names s)]
      [`(#:batch ,ss ,_ ...) (set-add-list names (cast ss (Listof Symbol)))]
      [`(,(? symbol? s) ,_ ...) (set-add names s)]
      [_ names])))


;; Conservative subset of operators' ranges.
(define prim-ranges
  (for/fold ([m : (HashTable Symbol Symbol) (hasheq)])
            ([dec (in-list prims:prims)])
    (match dec
      [`(#:pred ,(? symbol? s) ,_ ...) (hash-set m s 'boolean?)]
      [`(#:batch (,ss ...) (,_ ... . -> . ,(? symbol? r)) ,_ ...)
       (for/fold ([m : (HashTable Symbol Symbol) m])
                 ([s ss])
         (hash-set m (assert s symbol?) r))]
      [`(,(? symbol? s)
         (,_ ... . -> . ,(? symbol? r))
         ,_ ...)
       (hash-set m s r)]
      [_ m])))

;; Return refinements needed in operator's arguments in order for range to be satisfied
(define prim-refinements-for-ranges
  (let ()
    (define h∅ : (HashTable Symbol (Listof Symbol)) (hasheq))

    (: upd : (HashTable Symbol (HashTable Symbol (Listof Symbol))) Symbol Symbol (Listof Symbol)
       → (HashTable Symbol (HashTable Symbol (Listof Symbol))))
    (define (upd m f d cs)
      (hash-update m f
                   (λ ([refs : (HashTable Symbol (Listof Symbol))])
                     (hash-set refs d cs))
                   (λ () h∅)))

    (: on-refinements : (HashTable Symbol (HashTable Symbol (Listof Symbol))) Symbol (Listof Any)
                         → (HashTable Symbol (HashTable Symbol (Listof Symbol))))
    (define (on-refinements m s refs)
      (for/fold ([m : (HashTable Symbol (HashTable Symbol (Listof Symbol))) m])
                ([ref refs])
        (match ref
          [`(,(? symbol? cs) ... . -> . ,(? symbol? d))
           (upd m s d (cast cs (Listof Symbol)))]
          [_ m])))

    (for/fold ([m : (HashTable Symbol (HashTable Symbol (Listof Symbol))) (hasheq)])
              ([dec (in-list prims:prims)])
      (match dec
        [`(#:batch (,(? symbol? ss) ...) ,_ ,refinements ...)
         (for/fold ([m : (HashTable Symbol (HashTable Symbol (Listof Symbol))) m])
                   ([s ss])
           (on-refinements m (assert s symbol?) refinements))]
        [`(,(? symbol? s) ,_ ,refinements ...)
         (on-refinements m s refinements)]
        [_ m]))))
  

;; FIXME: some predicates about vectors and streams and such shouldn't be here...
(define base-predicates
  (for/fold ([acc : (℘ Symbol) {seteq #|HACK|# '<= '< '>= '> '=}])
            ([dec : Any (in-list prims:prims)])
    (match dec
      [`(#:pred ,(? symbol? s))
       (set-add acc s)]
      [`(,(? symbol? s) (any/c . -> . boolean?) ,_ ...)
       (set-add acc s)]
      [`(#:batch (,(? symbol? ss) ...) (any/c . -> . boolean?) ,_ ...)
       (set-add-list acc (cast ss (Listof Symbol)))]
      [_ acc])))

;; Ignore predicates without TR bindings
(define ignore-for-now?
  (set->predicate
   (list->set
    '(procedure? vector?
      pseudo-random-generator-vector? non-empty-string? string-contains?
      string-prefix? string-suffix? placeholder? hash-placeholder?
      stream? generator? 
      set-equal? set-eqv? set-eq? set-mutable? set-weak? normalized-arity?
      printable/c unsupplied-arg? contract? chaperone-contract? impersonator-contract?
      flat-contract? list-contract? has-contract? has-blame?
      even? odd? char-general-category
      dict?))))
