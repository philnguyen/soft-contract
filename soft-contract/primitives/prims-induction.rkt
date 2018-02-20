#lang typed/racket/base

(provide prims-induction@)

(require racket/match
         racket/contract
         typed/racket/unit
         racket/set
         unreachable
         set-extras
         "../utils/pretty.rkt"
         "../utils/patterns.rkt"
         "../utils/debug.rkt"
         "../runtime/signatures.rkt"
         "../reduction/signatures.rkt"
         "../ast/signatures.rkt"
         "signatures.rkt"
         "def.rkt"
         (for-syntax racket/base
                     racket/syntax
                     syntax/parse))

(define-unit prims-induction@
  (import prim-runtime^ ast-pretty-print^ pretty-print^ env^ sto^ compile^ kont^)
  (export)
  

  #|
  (induct-on C) ==>
  (->i (#|major premise |# [x C]
        #|motive        |# [P (C . -> . contract?)]
        #|minor premises|# [on-case-i {P} (->i ([x-i C-i] ... [ih-j (P x-j)] ...)
                                               (_ {x-i ...} (P (K x-i ...))))])
       (_ {x P} (P x)))
  |#
  (def (induct-on ℓ Vs H φ Σ ⟦k⟧)
    #:init ([C^ contract?])

    (: err : String -V → (℘ -ς))
    (define (err msg V)
      (define blm (-blm (ℓ-src ℓ) 'induct-on (list (string->symbol msg)) (list {set V}) ℓ))
      (⟦k⟧ blm H φ Σ))

    (: gen-name : Symbol (Listof -st-ac) → Symbol)
    (define (gen-name x path)
      (foldr
       (λ ([ac : -st-ac] [pref : Symbol])
         (format-symbol "~a.~a" pref (show-o ac)))
       x
       path))

    (: ⟦shape⟧ : -⟦e⟧ Symbol Shape → -⟦e⟧)
    (define (⟦shape⟧ ⟦P⟧ case-name s)
      (match-define (Shape xs m ⟦e⟧) s)
      (mk-->i (for/list : (Listof -⟦dom⟧) ([x (in-list xs)])
                (hash-ref m x))
              (let* ([ℓᵣ (ℓ-with-id ℓ case-name)]
                    [ℓₐ (ℓ-with-id ℓᵣ 'app)])
                (-⟦dom⟧ '_ xs (mk-app ℓₐ ⟦P⟧ (list ⟦e⟧)) ℓᵣ))))

    (: recombine-shape : -𝒾 (Listof -st-ac) (Listof Shape) → Shape)
    (define (recombine-shape 𝒾 path shapes)
      (define-values (var-lists maps exprs)
        (for/lists ([var-lists : (Listof (Listof Symbol))]
                    [maps : (Listof (Immutable-HashTable Symbol -⟦dom⟧))]
                    [exprs : (Listof -⟦e⟧)])
                   ([s (in-list shapes)])
          (match-define (Shape xs m e) s)
          (values xs m e)))
      (Shape (apply append var-lists)
             (for*/fold ([acc : (Immutable-HashTable Symbol -⟦dom⟧) (hasheq)])
                        ([m (in-list maps)] [(k v) (in-hash m)])
               (hash-set acc k v))
             (mk-app (ℓ-with-id ℓ path) (mk-V (-st-mk 𝒾)) exprs)))

    (: gen-shape : -x/C -⟦e⟧ -V → Shape)
    (define (gen-shape C-ind ⟦P⟧ C)
      (let go ([path : (Listof -st-ac) '()] [C : -V C])
        (define (gen)
          (define x (gen-name 'x path))
          (define ⟦x⟧ (↓ₓ 'induct-on x ℓ))
          (values x ⟦x⟧ (-⟦dom⟧ x #f (mk-V C) (ℓ-with-id ℓ x))))
        (match C
          [(== C-ind)
           (define-values (x ⟦x⟧ ⟦dom-x⟧) (gen))
           (define ⟦P-x⟧ (mk-app ℓ ⟦P⟧ (list ⟦x⟧)))
           (define xᵢₕ (format-symbol "ih_~a" x))
           (define ⟦dom-ih⟧ (-⟦dom⟧ xᵢₕ (list x) ⟦P-x⟧ (ℓ-with-id ℓ xᵢₕ)))
           (Shape (list x xᵢₕ) (hasheq x ⟦dom-x⟧ xᵢₕ ⟦dom-ih⟧) ⟦x⟧)]
          [(-St/C _ 𝒾 αℓs)
           (recombine-shape
            𝒾
            path
            (for/list ([αℓ (in-list αℓs)] [i (in-naturals)] #:when (index? i))
              (match-define {singleton-set Cᵢ} (σ@ Σ (-φ-cache φ) (-⟪α⟫ℓ-addr αℓ)))
              (go (cons (-st-ac 𝒾 i) path) Cᵢ)))]
          [_
           (define-values (x ⟦x⟧ ⟦dom-x⟧) (gen))
           (Shape (list x) (hasheq x ⟦dom-x⟧) ⟦x⟧)])))
    
    (: gen-cases : -x/C -⟦e⟧ -V → (Listof -⟦dom⟧))
    (define (gen-cases C-ind ⟦P⟧ C)
      (let go ([C : -V C] [ith : Natural 0])
        (match C
          [(-Or/C _ (-⟪α⟫ℓ α₁ _) (-⟪α⟫ℓ α₂ _))
           (match-define {singleton-set C₁} (σ@ Σ (-φ-cache φ) α₁))
           (match-define {singleton-set C₂} (σ@ Σ (-φ-cache φ) α₂))
           (define doms₁ (go C₁ ith))
           (define doms₂ (go C₂ (+ ith (length doms₁))))
           (append doms₁ doms₂)]
          [_
           (define case-name (format-symbol "case-~a" ith))
           (define ⟦c⟧ (⟦shape⟧ ⟦P⟧ case-name (gen-shape C-ind ⟦P⟧ C)))
           (define dom (-⟦dom⟧ case-name '{P} ⟦c⟧ (ℓ-with-id ℓ case-name)))
           (list dom)])))

    (: induct : -V → (℘ -ς))
    (define induct
      (match-lambda
        [(and C (-x/C α))
         (match-define {singleton-set C*} (σ@ Σ (-φ-cache φ) α))
         (define ⟦c⟧
           (let* ([⟦C⟧ (mk-V C)]
                  [⟦P⟧ (↓ₓ 'induct-on 'P ℓ)]
                  [⟦x⟧ (list (↓ₓ 'induct-on 'x ℓ))])
             (mk-->i (list* (-⟦dom⟧ 'x #f ⟦C⟧ ℓ)
                            (-⟦dom⟧ 'P #f (mk--> (ℓ-with-id ℓ 'P) (list ⟦C⟧) (mk-V 'contract?)) (ℓ-with-id ℓ 'mk-P))
                            (gen-cases C ⟦P⟧ C*))
                     (-⟦dom⟧ '_ '{x P} (mk-app ℓ ⟦P⟧ ⟦x⟧) (ℓ-with-id ℓ 'concl)))))
         (printf "generated induction principle: ~a~n" (show-⟦e⟧ ⟦c⟧))
         (⟦c⟧ ⊥ρ H φ Σ ⟦k⟧)]
        [C (err "inductive contract" C)]))
    
    (for/union : (℘ -ς) ([C (in-set C^)]) (induct C)))

  (def trivial (->* () #:rest list? any/c)))

(struct Shape ([order : (Listof Symbol)]
               [maps : (Immutable-HashTable Symbol -⟦dom⟧)]
               [expr : -⟦e⟧])
      #:transparent)
