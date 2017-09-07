#lang typed/racket/base

(require racket/match
         racket/contract
         racket/bool
         racket/string
         racket/math
         racket/list
         racket/stream
         racket/dict
         racket/function
         racket/set
         racket/flonum
         racket/fixnum
         racket/generator
         racket/random
         racket/format
         racket/splicing
         typed/racket/unit
         syntax/parse/define
         set-extras
         "../utils/debug.rkt"
         (except-in "../ast/signatures.rkt" normalize-arity arity-includes?)
         "signatures.rkt"
         "def.rkt"
         (for-syntax racket/base
                     racket/syntax
                     syntax/parse))

(provide prims-04-09@)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;; 4.9 Pairs and Lists
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define-unit prims-04-09@
  (import prim-runtime^)
  (export)


  ;; 4.9.1 Constructors and Selectors

  (def-pred null?)
  (def-alias-internal cons? -cons?)
  (def-alias-internal cons -cons)
  (def-alias-internal car -car)
  (def-alias-internal cdr -cdr)
  (def-alias-internal set-mcdr! -set-cdr!) ;; HACK for running some Scheme programs
  (def-const null)
  (def list? (any/c . -> . boolean?))
  (def list (∀/c (α) (() #:rest (listof α) . ->* . (listof α))))
  (def list* (() #:rest list? . ->* . list?)) ; FIXME
  (def build-list (∀/c (α) (exact-nonnegative-integer?
                            (exact-nonnegative-integer? . -> . α)
                            . -> . (listof α))))

  ;; 4.9.2 List Operations
  (def length (list? . -> . exact-nonnegative-integer?)
    #:refinements
    (pair? . -> . exact-positive-integer?)
    (null? . -> . zero?))
  (def list-ref (∀/c (α) ((and/c (listof α) pair?) exact-nonnegative-integer? . -> . α))) ; FIXME mismatch
  (def list-tail (∀/c (α) ((listof α) exact-nonnegative-integer? . -> . (listof α)))) ; FIXME mismatch
  (def append (∀/c (α) (() #:rest (listof (listof α)) . ->* . (listof α))))
  (def reverse (∀/c (α) ((listof α) . -> . (listof α))))

  ;; 4.9.3 List Iteration
  (def map (∀/c (α β) ((α . -> . β) (listof α) . -> . (listof β)))) ; FIXME uses
  (def andmap (∀/c (α) ((α . -> . any/c) (listof α) . -> . any/c))) ; FIXME uses
  (def ormap (∀/c (α) ((α . -> . any/c) (listof α) . -> . any/c))) ; FIXME uses
  (def for-each (∀/c (α) ((α . -> . any/c) (listof α) . -> . void?))) ; FIXME uses
  (def foldl (∀/c (α β) ((α β . -> . β) β (listof α) . -> . β))) ; FIXME uses
  (def foldr (∀/c (α β) ((α β . -> . β) β (listof α) . -> . β))) ; FIXME uses

  ;; 4.9.4 List Filtering
  (def filter (∀/c (α) ((α . -> . any/c) (listof α) . -> . (listof α))))
  (def remove
    (∀/c (α β)
         (case->
          [β (listof α) . -> . (listof α)]
          [β (listof α) (α β . -> . any/c) . -> . (listof α)])))
  (def* (remq remv) (∀/c (α) (any/c (listof α) . -> . (listof α))))
  (def remove*
    (∀/c (α β)
      (case->
       ((listof β) (listof α) . -> . (listof α))
       ((listof β) (listof α) (α β . -> . any/c) . -> . (listof α)))))
  (def* (remq* remv*) (∀/c (α) (list? (listof α) . -> . (listof α))))
  (def sort ; FIXME uses
    (∀/c (α) ((listof α) (α α . -> . any/c) . -> . (listof α))))

  ;; 4.9.5 List Searching
  (def member
    (∀/c (α β)
         (case->
          [β (listof α) . -> . (or/c (and/c (listof α) pair?) not)]
          [β (listof α) (α β . -> . any/c) . -> . (or/c (and/c (listof α) pair?) not)])))
  (def* (memv memq) (∀/c (α) (any/c (listof α) . -> . (or/c (and/c (listof α) pair?) not))))
  (def memf (∀/c (α) ((α . -> . any/c) (listof α) . -> . (or/c (and/c (listof α) pair?) not))))
  (def findf (∀/c (α) ((α . -> . any/c) (listof α) . -> . (or/c α not))))
  (def assoc
    (∀/c (α β)
         (case->
          [α (listof (cons/c α β)) . -> . (or/c (cons/c α β) not)]
          [α (listof (cons/c α β)) (α α . -> . any/c) . -> . (or/c (cons/c α β) not)])))
  (def* (assv assq) (∀/c (α β) (α (listof (cons/c α β)) . -> . (or/c (cons/c α β) not))))
  (def assf (∀/c (α β) ((α . -> . any/c) (listof (cons/c α β)) . -> . (or/c (cons/c α β) not))))

  ;; 4.9.6 Pair Acesssor Shorthands
  ; FIXME parametric
  (def* (caar cdar)
    ((cons/c pair? any/c) . -> . any/c))
  (def* (cadr cddr)
    ((cons/c any/c pair?) . -> . any/c))
  (def caaar
    ((cons/c (cons/c pair? any/c) any/c) . -> . any/c))
  (def caadr
    ((cons/c any/c (cons/c pair? any/c)) . -> . any/c))
  (def cadar
    ((cons/c (cons/c any/c pair?) any/c) . -> . any/c))
  (def caddr
    ((cons/c any/c (cons/c any/c pair?)) . -> . any/c))
  (def cdaar
    ((cons/c (cons/c pair? any/c) any/c) . -> . any/c))
  (def cdadr
    ((cons/c any/c (cons/c pair? any/c)) . -> . any/c))
  (def cddar
    ((cons/c (cons/c any/c pair?) any/c) . -> . any/c))
  (def cdddr
    ((cons/c any/c (cons/c any/c pair?)) . -> . any/c))
  ; TODO rest of them

  ;; 4.9.7 Additional List Functions and Synonyms
  (def-alias empty null)
  (def-alias pair? cons?)
  (def-alias empty? null?)
  (def-alias-internal first -car) ; FIXME precond
  (def-alias-internal rest -cdr) ; FIXME precond
  ;; FIXME parametric
  (def second
    ((cons/c any/c (cons/c any/c list?)) . -> . any/c))
  (def third
    ((cons/c any/c (cons/c any/c (cons/c any/c list?))) . -> . any/c))
  (def fourth
    ((cons/c any/c (cons/c any/c (cons/c any/c (cons/c any/c list?)))) . -> . any/c))
  (def fifth
    ((cons/c any/c (cons/c any/c (cons/c any/c (cons/c any/c (cons/c any/c list?))))) . -> . any/c))
  (def sixth
    ((cons/c any/c (cons/c any/c (cons/c any/c (cons/c any/c (cons/c any/c (cons/c any/c list?)))))) . -> . any/c))
  (def seventh
    ((cons/c any/c (cons/c any/c (cons/c any/c (cons/c any/c (cons/c any/c (cons/c any/c (cons/c any/c list?))))))) . -> . any/c))
  (def eighth
    ((cons/c any/c (cons/c any/c (cons/c any/c (cons/c any/c (cons/c any/c (cons/c any/c (cons/c any/c (cons/c any/c list?)))))))) . -> . any/c))
  (def ninth
    ((cons/c any/c (cons/c any/c (cons/c any/c (cons/c any/c (cons/c any/c (cons/c any/c (cons/c any/c (cons/c any/c (cons/c any/c list?))))))))) . -> . any/c))
  (def tenth
    ((cons/c any/c (cons/c any/c (cons/c any/c (cons/c any/c (cons/c any/c (cons/c any/c (cons/c any/c (cons/c any/c (cons/c any/c (cons/c any/c list?)))))))))) . -> . any/c))
  (def last (∀/c (α) ((and/c (listof α) pair?) . -> . α)))
  (def last-pair
    ; FIXME allowing recursive contract in DSL
    ; (∀/c (α β) ((μ (X) (or/c (cons/c α β) (cons/c α X))) . -> . (cons/c α β)))
    (pair? . -> . pair?))
  (def make-list (∀/c (α) (exact-nonnegative-integer? α . -> . (listof α))))
  (def list-update (∀/c (α) ((listof α) exact-nonnegative-integer? (α . -> . α) . -> . (listof α))))
  (def list-set (∀/c (α) ((listof α) exact-nonnegative-integer? α . -> . (listof α))))
  (def take (∀/c (α) ((listof α) exact-nonnegative-integer? . -> . (listof α)))) ; FIXME mismatch
  (def drop (∀/c (α) ((listof α) exact-nonnegative-integer? . -> . (listof α)))) ; FIXME mismatch
  (def split-at (∀/c (α) ((listof α) exact-nonnegative-integer? . -> . (values (listof α) (listof α))))) ; FIXME mismatch
  (def* (takef dropf) (∀/c (α) ((listof α) (α . -> . any/c) . -> . (listof α)))) ; FIXME mismatch
  (def splitf-at (∀/c (α) ((listof α) (α . -> . any/c) . -> . (values (listof α) (listof α))))) ; FIXME mismatch
  (def* (take-right drop-right) (∀/c (α) ((listof α) exact-nonnegative-integer? . -> . (listof α)))) ; FIXME mismatch
  (def split-at-right (∀/c (α) ((listof α) exact-nonnegative-integer? . -> . (values (listof α) (listof α))))) ; FIXME mismatch
  (def* (takef-right dropf-right) (∀/c (α) ((listof α) (α . -> . any/c) . -> . (listof α)))) ; FIXME mismatch
  (def splitf-at-right (∀/c (α) ((listof α) (α . -> . any/c) . -> . (values (listof α) (listof α))))) ; FIXME mismatch
  (def list-prefix?
    (∀/c (α)
         (case->
          [(listof α) (listof α) . -> . boolean?]
          [(listof α) (listof α) (α α . -> . any/c) . -> . boolean?])))
  (def* (take-common-prefix drop-common-prefix)
    (∀/c (α)
         (case->
          [(listof α) (listof α) . -> . (listof α)]
          [(listof α) (listof α) (α α . -> . any/c) . -> . (listof α)])))
  (def split-common-prefix
    (∀/c (α)
         (case->
          [(listof α) (listof α) . -> . (values (listof α) (listof α) (listof α))]
          [(listof α) (listof α) (α α . -> . any/c) . -> . (values (listof α) (listof α) (listof α))])))
  (def add-between (∀/c (α) ((listof α) α . -> . (listof α))))
  #;[append* ; FIXME uses ; FIXME listof
     ((listof list?) . -> . list?)]
  (def flatten (any/c . -> . list?))
  (def check-duplicates ; FIXME uses
    (∀/c (α)
         (case->
          [(listof α) . -> . (or/c α not)]
          [(listof α) (α α . -> . any/c) . -> . (or/c α not)])))
  (def remove-duplicates ; FIXME uses
    (∀/c (α)
         (case->
          [(listof α) . -> . (listof α)]
          [(listof α) (α α . -> . any/c) . -> . (listof α)])))
  (def filter-map (∀/c (α β) ((α . -> . β) (listof α) . -> . (listof (and/c β (not/c not))))))  ; FIXME uses
  (def count (∀/c (α) ((α . -> . any/c) (listof α) . -> . exact-nonnegative-integer?)))  ; FIXME varargs
  (def partition (∀/c (α) ((α . -> . any/c) (listof α) . -> . (values (listof α) (listof α)))))
  (def range
    (case->
     [real? . -> . (listof real?)]
     [real? real? . -> . (listof real?)]
     [real? real? real? . -> . (listof real?)]))
  (def append-map (∀/c (α β) ((α . -> . (listof β)) (listof α) . -> . (listof β)))) ; FIXME varargs
  (def filter-not (∀/c (α) ((α . -> . any/c) (listof α) . -> . (listof α))))
  (def shuffle (∀/c (α) ((listof α) . -> . (listof α))))
  (def permutations (∀/c (α) ((listof α) . -> . (listof (listof α)))))
  (def in-permutations (list? . -> . sequence?))
  (def* (argmin argmax) (∀/c (α) ((α . -> . real?) (and/c (listof α) pair?) . -> . α)))
  (def group-by
    (∀/c (α β)
         (case->
          [(α . -> . β) (listof α) . -> . (listof (listof α))]
          [(α . -> . β) (listof α) (β β . -> . any/c) . -> . (listof (listof α))])))
  (def cartesian-product (∀/c (α β) ((listof α) (listof β) . -> . (listof (list/c α β))))) ; FIXME varargs
  (def* (remf remf*) (∀/c (α) ((α . -> . any/c) (listof α) . -> . (listof α))))

  ;; 4.9.8 Immutable Cyclic Data
  (def make-reader-graph (any/c . -> . any/c))
  (def-pred placeholder?)
  (def make-placeholder (any/c . -> . placeholder?))
  (def placeholder-set! (placeholder? any/c . -> . void?) #:lift-concrete? #f)
  (def placeholder-get (placeholder? . -> . any/c))
  (def-pred hash-placeholder?)
  (def* (make-hash-placeholder make-hasheq-placeholder make-hasheqv-placeholder)
      ((listof pair?) . -> . hash-placeholder?))
  )
