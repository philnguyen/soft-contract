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
         "../utils/function.rkt"
         (except-in "../ast/signatures.rkt" normalize-arity arity-includes?)
         "../runtime/signatures.rkt"
         "../execution/signatures.rkt"
         "../signatures.rkt"
         "signatures.rkt"
         "def.rkt"
         (for-syntax racket/base
                     racket/syntax
                     syntax/parse))

(provide prims-04-13@)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;; 4.13 Hash Tables
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define-unit prims-04-13@
  (import sto^
          prim-runtime^
          exec^
          prover^)
  (export)

  (def-pred hash?)
  (def* (hash-equal? hash-eqv? hash-eq? hash-weak?)
    (hash? . -> . boolean?))

  (splicing-local
      ((: hash-helper : Σ ℓ W Symbol -o → (Values R (℘ Err)))
       (define (hash-helper Σ ℓ Wₓ name eq)
         (cond
           [(null? Wₓ) (just (Empty-Hash))]
           [(even? (length Wₓ))
            (define αₖ (α:dyn (β:hash:key ℓ) H₀))
            (define αᵥ (α:dyn (β:hash:val ℓ) H₀))
            (define ΔΣ₀ : ΔΣ
              (let go ([W : W Wₓ] [acc : ΔΣ ⊥ΔΣ])
                (match W
                  [(list* Vₖ Vᵥ W*)
                   (go W* (⧺ acc (alloc αₖ Vₖ) (alloc αᵥ Vᵥ)))]
                  [_ acc])))
            (just (Hash-Of αₖ αᵥ) ΔΣ₀)]
           [else (err (Err:Raised "even number of args" ℓ))])))
    (def (hash Σ ℓ W)
      #:init ()
      #:rest [W (listof any/c)]
      (hash-helper Σ ℓ W 'hash 'hash-equal?))
    (def (hasheq Σ ℓ W)
      #:init ()
      #:rest [W (listof any/c)]
      (hash-helper Σ ℓ W 'hasheq 'hash-eq?))
    (def (hasheqv Σ ℓ W)
      #:init ()
      #:rest [W (listof any/c)]
      (hash-helper Σ ℓ W 'hasheqv 'hash-eqv?)))

  (def make-hash
    (∀/c (α β)
         (case->
          [-> (and/c hash? hash-equal? hash-empty? (not/c immutable?))]
          [(listof (cons/c α β)) . -> . (and/c hash? hash-equal? (not/c immutable?) (hash/c α β))])))
  (def make-hasheqv
    (∀/c (α β)
         (case->
          [-> (and/c hash? hash-eqv? hash-empty? (not/c immutable?))]
          [(listof (cons/c α β)) . -> . (and/c hash? hash-eqv? (not/c immutable?) (hash/c α β))])))
  (def make-hasheq
    (∀/c (α β)
         (case->
          [-> (and/c hash? hash-eq? hash-empty? (not/c immutable?))]
          [(listof (cons/c α β)) . -> . (and/c hash? hash-eq? (not/c immutable?) (hash/c α β))])))
  (def make-immutable-hash
    (∀/c (α β)
         (case->
          [-> (and/c hash? hash-equal? hash-empty? immutable?)]
          [(listof (cons/c α β)) . -> . (and/c hash? hash-equal? immutable? (hash/c α β))])))
  (def make-immutable-hasheqv
    (∀/c (α β)
         (case->
          [-> (and/c hash? hash-eqv? hash-empty? immutable?)]
          [(listof (cons/c α β)) . -> . (and/c hash? hash-eqv? immutable? (hash/c α β))])))
  (def make-immutable-hasheq
    (∀/c (α β)
         (case->
          [-> (and/c hash? hash-eq? hash-empty? immutable?)]
          [(listof (cons/c α β)) . -> . (and/c hash? hash-eq? immutable? (hash/c α β))])))

  (def make-weak-hash
    (∀/c (α β)
         (case->
          (-> (and/c hash? hash-equal? hash-weak?))
          ((listof (cons/c α β)) . -> . (and/c hash? hash-equal? hash-weak? (hash/c α β))))))
  (def make-weak-hasheqv
    (∀/c (α β)
         (case->
          (-> (and/c hash? hash-equal? hash-weak?))
          ((listof (cons/c α β)) . -> . (and/c hash? hash-eqv? hash-weak? (hash/c α β))))))
  (def make-weak-hasheq
    (∀/c (α β)
         (case->
          (-> (and/c hash? hash-equal? hash-weak?))
          ((listof (cons/c α β)) . -> . (and/c hash? hash-eq? hash-weak? (hash/c α β))))))
  (def hash-set!
    (∀/c (α β) ((and/c (not/c immutable?) (hash/c α β)) α β . -> . void?)))
  (def hash-set*! ; FIXME uses
    (∀/c (α β) ((and/c (not/c immutable?) (hash/c α β)) α β . -> . void?)))
  (def hash-set
    (∀/c (α β)
      ((and/c immutable? (hash/c α β)) α β . -> . (and/c immutable? (hash/c α β)))))
  (def hash-set* ; FIXME uses
    (∀/c (α β)
      [(and/c immutable? (hash/c α β)) α β . -> . (and/c immutable? (hash/c α β))]))
  
  (def hash-ref
    (∀/c (α β)
         (case->
          [(hash/c α β) α . -> . β]
          [(hash/c α β) α (-> β) . -> . β])))
  
  (def hash-ref!
    (∀/c (α β) ((and/c (not/c immutable?) (hash/c α β)) α (-> β) . -> . void?)))
  (def hash-has-key?
    (∀/c (α β) ((hash/c α β) α . -> . boolean?)))
  (def hash-update!
    (∀/c (α β)
         (case->
          [(and/c (not/c immutable?) (hash/c α β)) α (β . -> . β) . -> . void?]
          [(and/c (not/c immutable?) (hash/c α β)) α (β . -> . β) (-> β) . -> . void?])))

  (def hash-update
    (∀/c (α β)
      ((and/c immutable? (hash/c α β)) α (β . -> . β) (-> β) . -> . (hash/c α β))))
  (def hash-remove!
    (∀/c (α β γ) ((and/c (not/c immutable?) (hash/c α β)) γ . -> . void?)))
  (def hash-remove
    (∀/c (α β γ) ((and/c immutable? (hash/c α β)) γ . -> . (hash/c α β))))
  (def hash-clear!
    (∀/c (α β) ((and/c (not/c immutable?) (hash/c α β)) . -> . void?)))
  (def hash-clear
    (∀/c (α β) ((and/c immutable? (hash/c α β)) . -> . (and/c immutable? hash? hash-empty?))))
  (def hash-copy-clear (∀/c (α β) ((hash/c α β) . -> . hash?)))
  (def hash-map
    (∀/c (α β γ)
         (case->
          [(hash/c α β) (α β . -> . γ) . -> . (listof γ)]
          [(hash/c α β) (α β . -> . γ) boolean? . -> . (listof γ)])))
  (def hash-keys (∀/c (α β) ((hash/c α β) . -> . (listof α))))
  (def hash-values (∀/c (α β) ((hash/c α β) . -> . (listof β))))
  (def hash->list (∀/c (α β) ((hash/c α β) . -> . (listof (cons/c α β)))))
  (def hash-for-each
    (∀/c (α β _)
         (case->
          [(hash/c α β) (α . -> . _) . -> . void?]
          [(hash/c α β) (α . -> . _) boolean? . -> . void?])))
  (def hash-count (hash? . -> . exact-nonnegative-integer?)
    #:refinements
    (hash-empty? . -> . 0))
  (def hash-empty? (∀/c (α β) ((hash/c α β) . -> . boolean?)))
  (def hash-iterate-first
    (∀/c (α β) ((hash/c α β) . -> . (or/c exact-nonnegative-integer? not))))
  (def hash-iterate-next
    (∀/c (α β) ((hash/c α β) exact-nonnegative-integer? . -> . (or/c exact-nonnegative-integer? not))))
  (def hash-iterate-key
    (∀/c (α β) ((hash/c α β) exact-nonnegative-integer? . -> . α)))
  (def hash-iterate-value
    (∀/c (α β) ((hash/c α β) exact-nonnegative-integer? . -> . β)))
  (def hash-iterate-key+value
    (∀/c (α β) ((hash/c α β) exact-nonnegative-integer? . -> . (values α β))))
  
  (def hash-copy
    (∀/c (α β) ((hash/c α β) . -> . (and/c (not/c immutable?) (hash/c α β)))))
  (def* (eq-hash-code eqv-hash-code equal-hash-code equal-secondary-hash-code)
    (∀/c (α) (α . -> . fixnum?)))

  ;; 4.13.1 Additional Hash Table Functions
  ; FIXME wtf is `hash-can-functional-set?`
  ;[hash-union ]
  ;[hash-union!]
  )
