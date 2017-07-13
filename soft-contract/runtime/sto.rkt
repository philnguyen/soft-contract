#lang typed/racket/base

(provide (all-defined-out))

(require typed/racket/unit
         racket/match
         racket/set
         set-extras
         "../utils/main.rkt"
         "../ast/definition.rkt"
         "signatures.rkt")

(define-unit sto@
  (import)
  (export sto^)

  (: σ@ : (U -Σ -σ) ⟪α⟫ → (℘ -V))
  (define (σ@ m ⟪α⟫)
    (define σ (if (-Σ? m) (-Σ-σ m) m))
    (with-debugging/off
      ((Vs)
       (hash-ref σ ⟪α⟫ (λ () (error 'σ@ "no address ~a" (⟪α⟫->-α ⟪α⟫)))))
      (when (>= (set-count Vs) 5)
        (printf "σ@: ~a -> ~a~n" (show-⟪α⟫ ⟪α⟫) (set-count Vs))
        (define-set roots : ⟪α⟫ #:eq? #t)
        (for ([V Vs])
          (roots-union! (V->⟪α⟫s V))
          (printf "  - ~a~n" (show-V V)))
        (printf "addresses:~n")
        (for ([(α Vs) (span-σ σ roots)])
          (printf "  - ~a ↦ ~a~n" (show-⟪α⟫ (cast α ⟪α⟫)) (set-map Vs show-V)))
        (printf "~n")
        (when (> ⟪α⟫ 3000)
          (error "DONE")))))

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

  (define ⟪α⟫ₕᵥ (-α->⟪α⟫ (-α.hv)))
  (define ⟪α⟫ₒₚ (-α->⟪α⟫ (-α.fn.●)))
  (define ⊥σ : -σ (hasheq ⟪α⟫ₕᵥ ∅))


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
  (define ⊤$* : -$* (hash))
  
  (: $-set! : -Σ -$ ⟪α⟫ -loc -W¹ → -$)
  (define ($-set! Σ $ α l W)
    (set-alias! Σ α l)
    (hash-set ($-del* $ (get-aliases Σ α)) l W))

  (: $-set*! : -Σ -$ (Listof ⟪α⟫) (Listof -loc) (Listof -W¹) → -$)
  (define ($-set*! Σ $ αs ls Ws)
    (for/fold ([$ : -$ $])
              ([α (in-list αs)]
               [l (in-list ls)]
               [W (in-list Ws)])
      ($-set! Σ $ α l W)))

  (: $-del : -$ -loc → -$)
  (define ($-del $ l) (hash-remove $ l))

  (: $@! : -Σ ⟪α⟫ -$ -loc → (℘ (Pairof -W¹ -$)))
  (define ($@! Σ α $ l)
    (cond [(hash-ref $ l #f) =>
           (λ ([W : -W¹]) {set (cons W $)})]
          [else (for/set: : (℘ (Pairof -W¹ -$)) ([V (in-set (σ@ Σ α))])
                  (define W (-W¹ V #f))
                  (cons W ($-set! Σ $ α l W)))]))

  (: $-extract : -$ (Sequenceof -loc) → -$*)
  (define ($-extract $ ls)
    (for/hash : -$* ([l ls])
      (values l (hash-ref $ l #f))))

  (: $-restore : -$ -$* → -$)
  (define ($-restore $ $*)
    (for/fold ([$ : -$ $])
              ([(l ?W) (in-hash $*)])
      (if ?W (hash-set #|instead of $-set|# $ l ?W) ($-del $ l))))

  (: $-del* : -$ (Sequenceof -loc) → -$)
  (define ($-del* $ ls)
    (for/fold ([$ : -$ $]) ([l ls])
      ($-del $ l)))


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
  
  )
