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
         "../reduction/signatures.rkt"
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
  (import prim-runtime^ widening^ pc^ val^ sto^ kont^ mon^)
  (export)

  (def-pred hash?)
  (def* (hash-equal? hash-eqv? hash-eq? hash-weak?)
    (hash? . -> . boolean?))

  (splicing-local
      ((: hash-helper : ℓ (Listof -W¹) -$ -Γ -⟪ℋ⟫ -Σ -⟦k⟧ Symbol -h → (℘ -ς))
       (define (hash-helper ℓ Ws $ Γ ⟪ℋ⟫ Σ ⟦k⟧ name eq)
         (define A
           (cond
             [(even? (length Ws))
              (define αₖ (-α->⟪α⟫ (-α.hash.key ℓ ⟪ℋ⟫)))
              (define αᵥ (-α->⟪α⟫ (-α.hash.val ℓ ⟪ℋ⟫)))
              (σ⊕Vs! Σ αₖ ∅)
              (σ⊕Vs! Σ αᵥ ∅)
              (let go! ([Ws : (Listof -W¹) Ws])
                (match Ws
                  [(list* Wₖ Wᵥ Ws*)
                   (σ⊕! Σ Γ αₖ Wₖ)
                   (σ⊕! Σ Γ αᵥ Wᵥ)
                   (go! Ws*)]
                  ['() (void)]))
              (define V (-Hash^ αₖ αᵥ #t))
              (-W (list V) (apply ?t@ name (map -W¹-t Ws)))]
             [else
              (define Cs (list (string->symbol "even number of arg(s)")))
              (define Vs (map -W¹-V Ws))
              (-blm (ℓ-src ℓ) name Cs Vs ℓ)]))
         (⟦k⟧ A $ Γ ⟪ℋ⟫ Σ)))
    (def (hash ℓ Ws $ Γ ⟪ℋ⟫ Σ ⟦k⟧)
      #:init ()
      #:rest [Ws (listof any/c)]
      (hash-helper ℓ Ws $ Γ ⟪ℋ⟫ Σ ⟦k⟧ 'hash 'hash-equal?))
    (def (hasheq ℓ Ws $ Γ ⟪ℋ⟫ Σ ⟦k⟧)
      #:init ()
      #:rest [Ws (listof any/c)]
      (hash-helper ℓ Ws $ Γ ⟪ℋ⟫ Σ ⟦k⟧ 'hasheq 'hash-eq?))
    (def (hasheqv ℓ Ws $ Γ ⟪ℋ⟫ Σ ⟦k⟧)
      #:init ()
      #:rest [Ws (listof any/c)]
      (hash-helper ℓ Ws $ Γ ⟪ℋ⟫ Σ ⟦k⟧ 'hasheqv 'hash-eqv?)))

  (def make-hash
    (∀/c (α β)
         (case->
          [-> (and/c hash? hash-equal? hash-empty? (not/c immutable?))]
          [(listof (cons/c α β)) . -> . (and/c (hash/c α β) hash-equal? (not/c immutable?))])))
  (def make-hasheqv
    (∀/c (α β)
         (case->
          [-> (and/c hash? hash-eqv? hash-empty? (not/c immutable?))]
          [(listof (cons/c α β)) . -> . (and/c (hash/c α β) hash-eqv? (not/c immutable?))])))
  (def make-hasheq
    (∀/c (α β)
         (case->
          [-> (and/c hash? hash-eq? hash-empty? (not/c immutable?))]
          [(listof (cons/c α β)) . -> . (and/c (hash/c α β) hash-eq? (not/c immutable?))])))
  (def make-immutable-hash
    (∀/c (α β)
         (case->
          [-> (and/c hash? hash-equal? hash-empty? immutable?)]
          [(listof (cons/c α β)) . -> . (and/c (hash/c α β) hash-equal? immutable?)])))
  (def make-immutable-hasheqv
    (∀/c (α β)
         (case->
          [-> (and/c hash? hash-eqv? hash-empty? immutable?)]
          [(listof (cons/c α β)) . -> . (and/c (hash/c α β) hash-eqv? immutable?)])))
  (def make-immutable-hasheq
    (∀/c (α β)
         (case->
          [-> (and/c hash? hash-eq? hash-empty? immutable?)]
          [(listof (cons/c α β)) . -> . (and/c (hash/c α β) hash-eq? immutable?)])))

  (def make-weak-hash
    (∀/c (α β)
         (case->
          (-> (and/c hash? hash-equal? hash-weak?))
          ((listof (cons/c α β)) . -> . (and/c (hash/c α β) hash-equal? hash-weak?)))))
  (def make-weak-hasheqv
    (∀/c (α β)
         (case->
          (-> (and/c hash? hash-equal? hash-weak?))
          ((listof (cons/c α β)) . -> . (and/c (hash/c α β) hash-eqv? hash-weak?)))))
  (def make-weak-hasheq
    (∀/c (α β)
         (case->
          (-> (and/c hash? hash-equal? hash-weak?))
          ((listof (cons/c α β)) . -> . (and/c (hash/c α β) hash-eq? hash-weak?)))))
  (def hash-set!
    (∀/c (α β) ((and/c (not/c immutable?) (hash/c α β)) α β . -> . void?)))
  (def hash-set*! ; FIXME uses
    (∀/c (α β) ((and/c (not/c immutable?) (hash/c α β)) α β . -> . void?)))
  (def (hash-set ℓ Ws $ Γ ⟪ℋ⟫ Σ ⟦k⟧)
    #:init ([Wₕ (and/c hash? immutable?)]
            [Wₖ any/c]
            [Wᵥ any/c])
    (match-define (-W¹ Vₕ tₕ) Wₕ)
    (match-define (-W¹ _  tₖ) Wₖ)
    (match-define (-W¹ _  tᵥ) Wᵥ)
    (define tₐ (?t@ 'hash-set tₕ tₖ tᵥ))
    (define αₖ* (-α->⟪α⟫ (-α.hash.key ℓ ⟪ℋ⟫)))
    (define αᵥ* (-α->⟪α⟫ (-α.hash.val ℓ ⟪ℋ⟫)))
    (match Vₕ
      [(-Hash^ αₖ αᵥ _)
       (σ-copy! Σ αₖ αₖ*)
       (σ-copy! Σ αᵥ αᵥ*)
       (σ⊕! Σ Γ αₖ* Wₖ)
       (σ⊕! Σ Γ αᵥ* Wᵥ)
       (define Wₕ* (-W (list (-Hash^ αₖ* αᵥ* #t)) tₐ))
       (⟦k⟧ Wₕ* $ Γ ⟪ℋ⟫ Σ)]
      [(-Hash/guard (and C (-Hash/C (-⟪α⟫ℓ αₖ ℓₖ) (-⟪α⟫ℓ αᵥ ℓᵥ))) αₕ ctx)
       (define ctx* (ctx-neg ctx))
       (define ⟦k⟧* (hash-set-inner∷ ℓ αₕ tₕ (wrap-hash∷ C ctx ⟦k⟧)))
       (for*/union : (℘ -ς) ([Cₖ (in-set (σ@ Σ αₖ))]
                             [Cᵥ (in-set (σ@ Σ αᵥ))])
          (mon (ctx-with-ℓ ctx* ℓₖ) (-W¹ Cₖ #f) Wₖ $ Γ ⟪ℋ⟫ Σ
               (mon*∷ ctx* (list (-W¹ Cᵥ #f)) (list Wᵥ) (list ℓᵥ) '() ⟦k⟧*)))]
      [_
       (define Wₕ* (-W (list (-Hash^ ⟪α⟫ₒₚ ⟪α⟫ₒₚ #t)) tₐ))
       (⟦k⟧ Wₕ* $ Γ ⟪ℋ⟫ Σ)]))
  (def hash-set* ; FIXME uses
    (∀/c (α β)
      [(and/c immutable? (hash/c α β)) α β . -> . (and/c (hash/c α β) immutable?)]))
  
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
  (def hash-count
    (∀/c (α β)
         (case->
          [(hash/c α β) . -> . exact-nonnegative-integer?]
          [(hash/c α β) boolean? . -> . exact-nonnegative-integer?])))
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
    (∀/c (α β) ((hash/c α β) . -> . (and/c (hash/c α β) (not/c immutable?)))))
  (def* (eq-hash-code eqv-hash-code equal-hash-code equal-secondary-hash-code)
    (∀/c (α) (α . -> . fixnum?)))

  ;; 4.13.1 Additional Hash Table Functions
  ; FIXME wtf is `hash-can-functional-set?`
  ;[hash-union ]
  ;[hash-union!]
  )
