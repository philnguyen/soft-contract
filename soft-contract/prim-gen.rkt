#lang typed/racket/base

(require racket/match racket/set "utils.rkt")
(require/typed "prims.rkt"
  [(implications prims:implications) (Listof Any)]
  [(prims prims:prims) (Listof Any)])

(provide Graph implications exclusions prim-ranges prim-refinements-for-ranges)

(define-type Graph (HashTable Symbol (Setof Symbol)))
(define -graph∅ : Graph (hasheq))

;; Compute a graph's reflexive-transitive closure
(: refl-trans : Graph → Graph)
(define (refl-trans m)

  ;; Compute `m`'s reflexive closure
  (define m₀
    (let ([refl : (Graph Symbol → Graph)
           (λ (m k)
             (hash-update m k (λ ([vs : (Setof Symbol)]) (set-add vs k)) →∅))])
      (for*/fold ([m : Graph m])
                 ([(l rs) (in-hash m)]
                  [m (in-value (refl m l))]
                  [r (in-set rs)])
        (refl m r))))

  ;; Compute `m`'s transitive closure
  (fix
   (λ ([m : Graph])
     (for/hash : Graph ([(l rs) (in-hash m)])
       (define rs*
         (for/fold ([rs* : (Setof Symbol) rs]) ([r rs])
           (∪ rs* (hash-ref m r))))
       (values l rs*)))
   m₀))

;; Add edge to graph
(: add-edge : Graph Symbol Symbol → Graph)
(define (add-edge m l r)
  (hash-update m l (λ ([rs : (Setof Symbol)]) (set-add rs r)) →∅))

;; Reverse a graph
(: reverse-graph : Graph → Graph)
(define (reverse-graph m)
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
    (define im*⁻¹ (reverse-graph im*))
    (define ex* ; ⟦a ⇒ ¬b, c ⇒ b⟧ ⇒ a ⇒ ¬c
      (for*/fold ([ex : Graph ex])
                 ([(l rs) (in-hash ex)]
                  [r (in-set rs)]
                  [r* (in-set (hash-ref im*⁻¹ r))])
        (add-edge (add-edge ex l r*) r* l)))
    (values im* ex*)))


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
(define prim-refinements-for-ranges : (HashTable Symbol (HashTable Symbol (Listof Symbol)))
  ;; TODO
  (hasheq))
