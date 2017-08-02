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
  (import pretty-print^)
  (export sto^)

  (: σ@ : (U -Σ -σ) ⟪α⟫ → (℘ -V))
  (define (σ@ m ⟪α⟫)
    (define σ (if (-Σ? m) (-Σ-σ m) m))
    (hash-ref σ ⟪α⟫ (λ () (error 'σ@ "no address ~a" (⟪α⟫->-α ⟪α⟫)))))

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

  (: σₖ@ : (U -Σ -σₖ) -αₖ → (℘ -⟦k⟧))
  (define (σₖ@ m αₖ)
    (hash-ref (if (-Σ? m) (-Σ-σₖ m) m) αₖ mk-∅eq))


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

  (: $-set : -$ -loc -W¹ → -$)
  (define $-set hash-set)
  
  (: $-set! : -Σ -$ ⟪α⟫ -loc -W¹ → -$)
  (define ($-set! Σ $ α l W)
    (set-alias! Σ α l)
    (hash-set ($-del* $ (get-aliases Σ α)) l W))

  (: $-set* : -$ (Listof -loc) (Listof -W¹) → -$)
  (define ($-set* $ ls Ws)
    (for/fold ([$ : -$ $])
              ([l (in-list ls)]
               [W (in-list Ws)])
      ($-set $ l W)))

  (: $-del : -$ -loc → -$)
  (define ($-del $ l) (hash-remove $ l))

  (: $@! : -Σ ⟪α⟫ -$ -loc → (℘ (Pairof -W¹ -$)))
  (define ($@! Σ α $ l)
    (cond [(hash-ref $ l #f) =>
           (λ ([W : -W¹]) {set (cons W $)})]
          [else #;(> (set-count (σ@ Σ α)) 1)
           (set-alias! Σ α l)
           #;(when (equal? l 'l)
             (let ([Vs (σ@ Σ α)])
               (printf "find ~a bindings at l, cache each to ⊘:~n" (set-count Vs))
               (for ([V (in-set Vs)])
                 (printf "- ~a~n" (show-V V)))))
           (for/set: : (℘ (Pairof -W¹ -$)) ([V (in-set (σ@ Σ α))])
             (define W (-W¹ V #f))
             (cons W ($-set $ l W)))]
          #;[else
           (when (equal? l 'l)
             (let ([Vs (σ@ Σ α)])
               (printf "find ~a bindings at l, cache each to ⊘:~n" (set-count Vs))
               (for ([V (in-set Vs)])
                 (printf "- ~a~n" (show-V V)))))
           (define V (set-first (σ@ Σ α)))
           {set (cons (-W¹ V #f) $)}]))

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
      [(-α.x x _) x]
      [(? -𝒾? 𝒾) 𝒾]
      [α₀ #f]))
  
  )
