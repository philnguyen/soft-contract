#lang typed/racket/base

(provide (all-defined-out))

(require typed/racket/unit
         racket/match
         racket/set
         racket/splicing
         set-extras
         "../utils/main.rkt"
         "../ast/signatures.rkt"
         "../proof-relation/signatures.rkt"
         "../primitives/signatures.rkt"
         "signatures.rkt")

(define-unit sto@
  (import pretty-print^ local-prover^ pc^ val^ prim-runtime^ static-info^)
  (export sto^)

  (splicing-local
      ((define ⟪null?⟫ (-⟪α⟫ℓ (-α->⟪α⟫ (-α.imm 'null?)) +ℓ₀))
       (define cache-listof : (Mutable-HashTable ⟪α⟫ (℘ -V)) (make-hasheq)))
    (: σ@ : (U -Σ -σ) ⟪α⟫ → (℘ -V))
    (define (σ@ m ⟪α⟫)
      (match (⟪α⟫->-α ⟪α⟫)
        [(-α.imm V) {set V}]
        [(-α.imm-listof x Cₑ ℓ)
         (hash-ref!
          cache-listof ⟪α⟫
          (λ ()
            (define flat? (C-flat? Cₑ))
            (define Cₚ (-St/C flat? -𝒾-cons
                              (list (-⟪α⟫ℓ (-α->⟪α⟫ (-α.imm Cₑ)) (ℓ-with-id ℓ 'elem))
                                    (-⟪α⟫ℓ (-α->⟪α⟫ (-α.imm-ref-listof x Cₑ ℓ)) (ℓ-with-id ℓ 'rec)))))
            {set (-Or/C flat? ⟪null?⟫ (-⟪α⟫ℓ (-α->⟪α⟫ (-α.imm Cₚ)) (ℓ-with-id ℓ 'pair)))}))]
        [(-α.imm-ref-listof x Cₑ ℓ)
         (hash-ref! cache-listof ⟪α⟫ (λ () {set (-x/C (-α->⟪α⟫ (-α.imm-listof x Cₑ ℓ)))}))]
        [α
         (define σ (if (-Σ? m) (-Σ-σ m) m))
         (hash-ref σ ⟪α⟫ (λ () (match α
                                 ; ok for hv addresses to not exist
                                 ; TODO clean up
                                 [(-α.hv _) ∅]
                                 [_ (error 'σ@ "no address ~a" (⟪α⟫->-α ⟪α⟫))])))])))

  (: defined-at? : (U -Σ -σ) ⟪α⟫ → Boolean)
  (define (defined-at? σ α)
    (cond [(-Σ? σ) (defined-at? (-Σ-σ σ) α)]
          [else (and (hash-has-key? σ α)
                     (not (∋ (hash-ref σ α) 'undefined)))]))

  (: σ-remove : -σ ⟪α⟫ -V → -σ)
  (define (σ-remove σ ⟪α⟫ V)
    (hash-update σ ⟪α⟫ (λ ([Vs : (℘ -V)]) (set-remove Vs V))))

  (: σ-remove! : -Σ ⟪α⟫ -V → Void)
  (define (σ-remove! Σ ⟪α⟫ V)
    (define σ (-Σ-σ Σ))
    (set--Σ-σ! Σ (σ-remove σ ⟪α⟫ V)))

  (: σ@/list : (U -Σ -σ) (Listof ⟪α⟫) → (℘ (Listof -V)))
  ;; Look up store at addresses. Return all possible combinations
  (define (σ@/list m ⟪α⟫s)
    (define σ (if (-Σ? m) (-Σ-σ m) m))
    (with-debugging/off
      ((ans)
       (let loop : (℘ (Listof -V)) ([⟪α⟫s : (Listof ⟪α⟫) ⟪α⟫s])
            (match ⟪α⟫s
              [(cons ⟪α⟫ ⟪α⟫s*)
               (define Vs (σ@ σ ⟪α⟫))
               (define Vss (loop ⟪α⟫s*))
               (for*/set: : (℘ (Listof -V)) ([V Vs] [Vs Vss])
                 (cons V Vs))]
              ['() {set '()}])))
      (when (> (set-count ans) 1)
        (printf "σ@/list: ~a -> ~a~n" (map show-⟪α⟫ ⟪α⟫s) (set-count ans)))))

  (: σ@¹ : (U -Σ -σ) ⟪α⟫ → -V)
  ;; Look up store, asserting that exactly 1 value resides there
  (define (σ@¹ m ⟪α⟫)
    (define Vs (σ@ m ⟪α⟫))
    (assert (= 1 (set-count Vs)))
    (set-first Vs))

  (define ⟪α⟫ₒₚ (-α->⟪α⟫ (-α.imm (-● ∅))))
  (define ⊥σ : -σ (hasheq))


  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
  ;;;;; Kontinuation store
  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (define ⊥σₖ : -σₖ (hash))

  (: σₖ@ : (U -Σ -σₖ) -αₖ → (℘ -κ))
  (define (σₖ@ m αₖ)
    (hash-ref (if (-Σ? m) (-Σ-σₖ m) m) αₖ mk-∅))


  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
  ;;;;; Memo table
  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
  (define ⊥M : -M (hash))
  
  (: M@ : (U -Σ -M) -αₖ → (℘ -ΓA))
  (define (M@ M α)
    (define m (if (-Σ? M) (-Σ-M M) M))
    (hash-ref m α mk-∅))


  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
  ;;;;; Cache
  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
  (define ⊤$ : -$ (hash))
  (define ⊤$* : -δ$ (hash))

  (: $-set : -$ -loc -?t → -$)
  (define ($-set $ l t)
    (if t (hash-set $ l t) $))
  
  (: $-set! : -Σ -$ ⟪α⟫ -loc -?t → -$)
  (define ($-set! Σ $ α l t)
    (cond [t
           (set-alias! Σ α l)
           (hash-set ($-del* $ (get-aliases Σ α)) l t)]
          [else $]))

  (: $-set* : -$ (Listof -loc) (Listof -?t) → -$)
  (define ($-set* $ ls ts)
    (for/fold ([$ : -$ $])
              ([l (in-list ls)]
               [t (in-list ts)])
      ($-set $ l t)))

  (: $-del : -$ -loc → -$)
  (define ($-del $ l) (hash-remove $ l))

  (: $@! : -Σ -Γ ⟪α⟫ -$ -loc ℓ → (Values (℘ -W¹) -$))
  (define ($@! Σ Γ α $ l ℓ)
    (define Vs (σ@ Σ α))
    (cond [(hash-ref $ l #f)
           =>
           (λ ([t : -t])
             (values (for/set: : (℘ -W¹) ([V (in-set Vs)]
                                          #:when (plausible-V-t? Γ V t))
                       (-W¹ V t))
                     $))]
          [else
           (define ℓ*
             (cond [(symbol? l) (if (assignable? l) ℓ (-t.x l))]
                   [(-𝒾? l) (if (assignable? l) ℓ l)]
                   [else ℓ]))
           (values (for/set: : (℘ -W¹) ([V (in-set Vs)])
                     (-W¹ V ℓ*))
                   ($-set $ l ℓ*))]))

  (: $-extract : -$ (Sequenceof -loc) → -δ$)
  (define ($-extract $ ls)
    (for/hash : -δ$ ([l ls])
      (values l (hash-ref $ l #f))))

  (: $-restore : -$ -δ$ → -$)
  (define ($-restore $ $*)
    (for/fold ([$ : -$ $])
              ([(l ?W) (in-hash $*)])
      (if ?W ($-set $ l ?W) ($-del $ l))))

  (: $-del* : -$ (Sequenceof -loc) → -$)
  (define ($-del* $ ls)
    (for/fold ([$ : -$ $]) ([l ls])
      ($-del $ l)))

  (: $↓ : -$ (℘ -loc) → -$)
  (define ($↓ $ ls)
    (for/fold ([$ : -$ $])
              ([(l W) (in-hash $)] #:unless (∋ ls l))
      (hash-remove $ l)))

  (: $-cleanup : -$ → -$)
  (define ($-cleanup $)
    (for/fold ([$ : -$ $])
              ([l (in-hash-keys $)]
               #:when (-loc.offset? l))
      (hash-remove $ l)))

  (: $-symbolic-names : -$ → (℘ (U Symbol ℓ)))
  (define ($-symbolic-names $)
    (for/unioneq : (℘ (U Symbol ℓ)) ([t (in-hash-values $)])
      (fvₜ t)))


  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
  ;;;;; Aliases
  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
  (define ⊥𝒜 : -𝒜 (hasheq))

  (: set-alias! : -Σ ⟪α⟫ -loc → Void)
  (define (set-alias! Σ α l)
    (set--Σ-𝒜! Σ (hash-update (-Σ-𝒜 Σ) α (λ ([ls : (℘ -loc)]) (set-add ls l)) mk-∅)))

  (: get-aliases : (U -Σ -𝒜) ⟪α⟫ → (℘ -loc))
  (define (get-aliases aliases α)
    (define 𝒜 (if (-Σ? aliases) (-Σ-𝒜 aliases) aliases))
    (hash-ref 𝒜 α mk-∅))

  (: hack:α->loc : ⟪α⟫ → (Option -loc))
  (define (hack:α->loc α)
    (match (⟪α⟫->-α α)
      [(-α.x x _ _) x]
      [(? -𝒾? 𝒾) 𝒾]
      [α₀ #f]))

  (: mutable? : ⟪α⟫ → Boolean)
  (define (mutable? ⟪α⟫)
    (match (⟪α⟫->-α ⟪α⟫)
      [(-α.x x _ _) (assignable? x)]
      [(-α.fld 𝒾 _ _ i) (struct-mutable? 𝒾 i)]
      [(? -α.idx?) #t]
      [_ #f]))
  
  )
