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
         racket/extflonum
         racket/generator
         racket/random
         racket/format
         racket/splicing
         typed/racket/unit
         syntax/parse/define
         set-extras
         "../utils/debug.rkt"
         (except-in "../ast/definition.rkt" normalize-arity arity-includes?)
         "../ast/shorthands.rkt"
         "../runtime/signatures.rkt"
         "../signatures.rkt"
         "signatures.rkt"
         "def-prim.rkt"
         (for-syntax racket/base
                     racket/syntax
                     syntax/parse))

(provide prims-04-13@)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;; 4.13 Hash Tables
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define-unit prims-04-13@
  (import prim-runtime^ proof-system^ widening^ val^ pc^ sto^ instr^)
  (export)

  (def-pred hash?)
  (def-prims (hash-equal? hash-eqv? hash-eq? hash-weak?)
    (hash? . -> . boolean?))

  (splicing-local
      ((define refinements : (℘ -h) {set 'hash? 'immutable?})
       (: hash-helper : -⟪ℋ⟫ -ℒ -Γ (Listof -W¹) Symbol -h → (℘ -ΓA))
       (define (hash-helper ⟪ℋ⟫ ℒ Γ Ws name eq)
         (define A
           (cond
             [(even? (length Ws))
              ;; FIXME: unsound until having real model for hashtable.
              ;; Cannot just havoc and widen
              (-W (list (-● (set-add refinements eq))) (apply ?t@ name (map -W¹-t Ws)))]
             [else
              (define-values (ℓ l) (unpack-ℒ ℒ))
              (-blm l name (list (string->symbol "even number of arg(s)")) (map -W¹-V Ws) ℓ)]))
         {set (-ΓA (-Γ-facts Γ) A)}))
    (def-prim/custom (hash ⟪ℋ⟫ ℒ Σ Γ Ws)
      (hash-helper ⟪ℋ⟫ ℒ Γ Ws 'hash 'hash-equal?))
    (def-prim/custom (hasheq ⟪ℋ⟫ ℒ Σ Γ Ws)
      (hash-helper ⟪ℋ⟫ ℒ Γ Ws 'hasheq 'hash-eq?))
    (def-prim/custom (hasheqv ⟪ℋ⟫ ℒ Σ Γ Ws)
      (hash-helper ⟪ℋ⟫ ℒ Γ Ws 'hasheqv 'hash-eqv?)))

  (splicing-local
      ((define refinements : (℘ -h) {set 'hash? (-not/c 'immutable?)})

       (define-syntax-parser define-make-hash
         [(_ make-hash:id eq:id)
          (define/with-syntax make-hash-1 (format-id #'make-hash "~a-1" (syntax-e #'make-hash)))
          (define/with-syntax .make-hash-1 (format-id #'make-hash ".~a-1" (syntax-e #'make-hash)))
          #'(begin
              (def-prim make-hash-1
                ((listof pair?) . -> . (and/c hash? (not/c immutable?) eq)))
              (def-prim/custom (make-hash ⟪ℋ⟫ ℒ Σ Γ Ws)
                (match Ws
                  ['() {set (-ΓA (-Γ-facts Γ) (-W (list (-● (set-add refinements 'eq)))
                                                  (apply ?t@ 'make-hash (map -W¹-t Ws))))}]
                  [_ (.make-hash-1 ⟪ℋ⟫ ℒ Σ Γ Ws)])))])
       )
    (define-make-hash make-hash equal?)
    (define-make-hash make-hasheqv eqv?)
    (define-make-hash make-hasheq eq?))

  (def-prim make-weak-hash ; FIXME uses ; FIXME listof
    (-> (and/c hash? hash-equal? hash-weak?)))
  (def-prim make-weak-hasheqv ; FIXME uses ; FIXME listof
    (-> (and/c hash? hash-eqv? hash-weak?)))
  (def-prim make-weak-hasheq ; FIXME uses ; FIXME listof
    (-> (and/c hash? hash-eq? hash-weak?)))
  (def-prim/todo hash-set!
    ((and/c hash? (not/c immutable?)) any/c any/c . -> . void?))
  (def-prim/todo hash-set*! ; FIXME uses
    ((and/c hash? (not/c immutable?)) any/c any/c . -> . void?))
  (def-prim/todo hash-set ; FIXME refine with `eq?` and `eqv?`
    ((and/c hash? immutable?) any/c any/c . -> . (and/c hash? immutable?)))
  (def-prim/todo hash-set* ; FIXME refine with `eq?` and `eqv?`
    ((and/c hash? immutable?) any/c any/c . -> . (and/c hash? immutable?)))
  (def-prim hash-ref ; FIXME uses
    (hash? any/c . -> . any/c))
  (def-prim hash-ref! ; FIXME precision
    (hash? any/c any/c . -> . any/c))
  (def-prim hash-has-key?
    (hash? any/c . -> . boolean?))
  (def-prim hash-update! ; FIXME uses
    ((and/c hash? (not/c immutable?)) any/c #|FIXME ext|# procedure? . -> . void?))
  (def-prim hash-update
    ((and/c hash? immutable?) any/c #|FIXME ext|# procedure? . -> . (and/c hash? immutable?)))
  (def-prim hash-remove!
    ((and/c hash? (not/c immutable?)) any/c . -> . void?))
  (def-prim hash-remove
    ((and/c hash? immutable?) any/c . -> . (and/c hash? immutable?)))
  (def-prim hash-clear!
    ((and/c hash? (not/c immutable?)) . -> . void?))
  (def-prim hash-clear
    ((and/c hash? immutable?) . -> . (and/c hash? immutable?)))
  (def-prim hash-copy-clear
    (hash? . -> . hash?))
  #;[hash-map ; FIXME uses ; FIXME listof
     (hash? (any/c any/c . -> . any/c) . -> . (listof any/c))]
  #;[hash-keys ; FIXME listof
     (hash? . -> . (listof any/c))]
  #;[hash-values ; FIXME listof
     (hash? . -> . (listof any/c))]
  #;[hash->list ; simplified from doc's `(cons/c any/c any/c)` ; FIXME listof
     (hash? . -> . (listof pair?))]
  (def-prim hash-for-each ; FIXME uses
    (hash? #|FIXME ext|# procedure? . -> . void?))
  (def-prim hash-count
    (hash? . -> . exact-nonnegative-integer?))
  (def-prim hash-empty?
    (hash? . -> . boolean?))
  (def-prim hash-iterate-first
    (hash? . -> . (or/c exact-nonnegative-integer? not)))
  (def-prim hash-iterate-next
    (hash? exact-nonnegative-integer? . -> . (or/c exact-nonnegative-integer? not)))
  (def-prims (hash-iterate-key hash-iterate-value)
    (hash? exact-nonnegative-integer? . -> . any/c))
  (def-prim hash-copy
    (hash? . -> . (and/c hash? (not/c immutable?))))
  (def-prims (eq-hash-code eqv-hash-code equal-hash-code equal-secondary-hash-code)
    (any/c . -> . fixnum?))

  ;; 4.13.1 Additional Hash Table Functions
  ; FIXME wtf is `hash-can-functional-set?`
  ;[hash-union ]
  ;[hash-union!]
  
  )
