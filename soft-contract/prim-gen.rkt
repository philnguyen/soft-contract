#lang racket/base

(require
 racket/match racket/contract racket/set "utils.rkt"
 (prefix-in prims: "prims.rkt"))

(provide
 graph?
 (contract-out
  [implications graph?]
  [exclusions graph?]))

(define graph? (hash/c symbol? (set/c symbol?)))

(define (fix f x)
  (define x* (f x))
  (if (equal? x x*) x (fix f x*)))

;; Compute a graph's reflexive-transitive closure
(define/contract (refl-trans m)
  (graph? . -> . graph?)

  ;; Compute `m`'s reflexive closure
  (define m₀
    (let ([refl (λ (m k) (hash-update m k (λ (vs) (set-add vs k)) ∅))])
      (for*/fold ([m m])
                 ([(l rs) (in-hash m)]
                  [m (in-value (refl m l))]
                  [r (in-set rs)])
        (refl m r))))

  ;; Compute `m`'s transitive closure
  (fix
   (λ (m)
     (for/hash ([(l rs) (in-hash m)])
       (define rs*
         (for/fold ([rs* rs]) ([r rs])
           (∪ rs* (hash-ref m r))))
       (values l rs*)))
   m₀))

;; Add edge to graph
(define/contract (add-edge m l r)
  (graph? symbol? symbol? . -> . graph?)
  (hash-update m l (λ (rs) (set-add rs r)) ∅))

;; Reverse a graph
(define/contract (reverse-graph m)
  (graph? . -> . graph?)
  (for*/fold ([m (hash)])
             ([(l rs) (in-hash m)] [r rs])
    (add-edge m r l)))

(define-values (implications exclusions)
  (let ()

    ;; Compute first versions of graphs to start with
    (define-values (im ex)
      (for/fold ([im (hash)] [ex (hash)])
                ([dec (in-list prims:implications)])
        (match dec
          [`(,l ⇒ ,r)
           (values (add-edge im l r) ex)]
          [`(#:partition ,r (,ls ...))
           (define im*
             (for/fold ([im im]) ([l ls])
               (add-edge im l r)))
           (define ex*
             (for*/fold ([ex ex]) ([l ls] [l* ls] #:unless (eq? l l*))
               (add-edge ex l l*)))
           (values im* ex*)]
          [`(#:exclusion ,ss ...)
           (define im* ; to make sure `im` graph covers every key
             (for/fold ([im im]) ([s ss])
               (add-edge im s s)))
           (define ex*
             (for*/fold ([ex ex]) ([s ss] [s* ss] #:unless (eq? s s*))
               (add-edge ex s s*)))
           (values im* ex*)])))
    
    (define im* (refl-trans im))
    (define im*⁻¹ (reverse-graph im*))
    (define ex* ; ⟦a ⇒ ¬b, c ⇒ b⟧ ⇒ a ⇒ ¬c
      (for*/fold ([ex ex])
                 ([(l rs) (in-hash ex)]
                  [r (in-set rs)]
                  [r* (in-set (hash-ref im*⁻¹ r))])
        (add-edge (add-edge ex l r*) r* l)))
    (values im* ex*)))
