#lang typed/racket/base

(provide #;reduction@)

(require racket/set
         racket/match
         racket/list
         typed/racket/unit
         set-extras
         "../utils/main.rkt"
         "../ast/signatures.rkt"
         "../runtime/signatures.rkt"
         "../proof-relation/signatures.rkt"
         "../primitives/signatures.rkt"
         "../signatures.rkt"
         "signatures.rkt"

         "compile.rkt"
         "app.rkt"
         "mon.rkt"
         "fc.rkt"
         "kont.rkt"
         "havoc.rkt"
         "memoize.rkt"
         "debugging.rkt"
         )

(define-unit pre-reduction@
  (import static-info^ path^ kont^ havoc^ app^ mon^ fc^ compile^ local-prover^ verifier^
          val^ for-gc^ env^ sto^ ast-pretty-print^ pretty-print^ instr^ summ^
          debugging^)
  (export reduction^)

  (define-type Ctx (Pairof -σ -σₖ))

  (: run : -⟦e⟧ → (Values (℘ -A) -Σ))
  (define (run ⟦e⟧)
    (define seen : (HashTable -ς Ctx) (make-hash))
    (define ℓ₀ (loc->ℓ (loc 'start 0 0 '())))
    (define αₖ₀ (-αₖ H∅ (-B (-Clo '() ⟦e⟧ ⊥ρ) '() ℓ₀) φ₀))
    (define Σ (-Σ ⊥σ (hash-set ⊥σₖ αₖ₀ ∅) ⊥Ξ))
    (define iter : Natural 0)
    (define ?max-steps (max-steps))
    (define iter-maxed? : (Natural → Boolean) (if ?max-steps (λ (i) (> i ?max-steps)) (λ _ #f)))

    ;; With side-effect adding to error set
    (let loop ([front : (℘ -ς) {set (-ς↑ αₖ₀)}] [ans : (℘ -A) ∅])
      (cond
        [(and (not (set-empty? front)) (not (iter-maxed? iter)))
         (define-values (ς↑s ς↓s ς!s) (partition-states front))

         (begin
           (when (debug-iter?)
             (printf "* ~a: ~a~n" iter (set-count front)))

           (when (debug-trace?)

             (begin ; interactive
               (define ςs-list
                 (append ς↑s ς↓s))
               (define ς->i
                 (for/hash : (HashTable -ς Integer) ([(ς i) (in-indexed ςs-list)])
                   (values ς i))))
             
             (printf " * evs:~n")
             (for ([ς ς↑s])
               (printf "  -[~a]. ~a~n" (hash-ref ς->i ς) (show-ς ς)))
             (printf " * rts:~n")
             (for ([ς ς↓s])
               (printf "  -[~a]. ~a~n" (hash-ref ς->i ς) (show-ς ς)))

             #;(begin ; interactive
                 (printf "~nchoose [0-~a|ok|done]: " (sub1 (hash-count ς->i)))
                 (match (read)
                   [(? exact-integer? i) (set! front (set (list-ref ςs-list i)))]
                   ['done (error "DONE")]
                   [_ (void)]))
             (printf "~n"))
           
           (set! iter (+ 1 iter)))

         (define next
           (match-let ([(-Σ σ σₖ _) Σ])
             (define vsn : Ctx (cons σ σₖ))

             (: ς↑-seen? : -ς↑ → Boolean)
             (define (ς↑-seen? ς)
               (cond [(hash-ref seen ς #f) =>
                      (match-lambda
                        [(cons σ₀ σₖ₀)
                         (define root
                           (match (-αₖ-block (-ς-ctx ς))
                             [(-B Vₕ Vₓs _) (∪ (->⟪α⟫s Vₕ) (->⟪α⟫s Vₓs))]
                             [(-M _ C V) (∪ (->⟪α⟫s C) (->⟪α⟫s V))]
                             [(-F _ _ C V) (∪ (->⟪α⟫s C) (->⟪α⟫s V))]
                             [(-HV tag) {seteq (-α->⟪α⟫ (-α.hv tag))}]))
                         (σ-equal?/spanning-root σ₀ σ root)])]
                     [else #f]))

             (: ς↓-seen? : -ς↓ → Boolean)
             (define (ς↓-seen? ς)
               (define (⟦k⟧->αₖs [⟦k⟧ : -⟦k⟧]) {set (⟦k⟧->αₖ ⟦k⟧)})
               (cond [(hash-ref seen ς #f) =>
                      (match-lambda
                        [(cons σ₀ σₖ₀)
                         (map-equal?/spanning-root σₖ₀ σₖ {set (-αₖ-block (-ς-ctx ς))} ⟦k⟧->αₖs)])]
                     [else #f]))

             (define next-from-ς↑s
               (↝↑! (for/list : (Listof -ς↑) ([ς ς↑s] #:unless (ς↑-seen? ς))
                      (hash-set! seen ς vsn)
                      ς)
                    Σ))
             (define next-from-ς↓s
               (↝↓! (for/list : (Listof -ς↓) ([ς ς↓s] #:unless (ς↓-seen? ς))
                      (hash-set! seen ς vsn)
                      ς)
                    Σ))
             (∪ next-from-ς↑s next-from-ς↓s)))
         (define ans*
           (for/fold ([ans : (℘ -A) ans]) ([ς (in-list ς!s)])
             (set-add ans (-ς!-blm ς))))
         (loop next ans*)]
        [else
         (match-define (-Σ σ σₖ _) Σ)
         (when (debug-iter?)
           (printf "|σ| = ~a, |σₖ| = ~a~n" (hash-count σ) (hash-count σₖ)))
         (when (and ?max-steps (> iter ?max-steps))
           (printf "Execution capped at ~a steps~n" ?max-steps))
         #;(print-large-sets Σ #:val-min 1 #:kont-min 1)
         (values ans Σ)])))

  (: ↝↑! : (Listof -ς↑) -Σ → (℘ -ς))
  ;; Quick-step on "push" state
  (define (↝↑! ςs Σ)
    (for/union : (℘ -ς) ([ς (in-list ςs)])
      (match-define (-ς↑ αₖ) ς)
      (define ⟦k⟧ (rt αₖ))
      (match-define (-αₖ H bl φ) αₖ)
      (match bl
        [(-B Vₕ Vₓs ℓ) (app₁ ℓ Vₕ Vₓs H φ Σ ⟦k⟧)]
        [(-M ctx C V) (mon ctx C V H φ Σ ⟦k⟧)]
        [(-F l ℓ C V) (flat-chk l ℓ C V H φ Σ ⟦k⟧)]
        [(-HV tag) (havoc tag φ Σ ⟦k⟧)]
        [_ (error '↝↑ "~a" bl)])))

  (: ↝↓! : (Listof -ς↓) -Σ → (℘ -ς))
  ;; Quick-step on "pop" state
  (define (↝↓! ςs Σ)
    (define σₖ (-Σ-σₖ Σ))
    (define σ (-Σ-σ Σ))
    (for/union : (℘ -ς) ([ς (in-list ςs)])
      (match-define (-ς↓ αₖₑₑ A φ) ς)
      (define H (-αₖ-instr αₖₑₑ))         
      (for/union : (℘ -ς) ([⟦k⟧ (in-set (σₖ@ σₖ αₖₑₑ))])
        (⟦k⟧ A H φ Σ))))

  (: partition-states : (℘ -ς) → (Values (Listof -ς↑) (Listof -ς↓) (Listof -ς!)))
  (define (partition-states ςs)
    (for/fold ([ς↑s : (Listof -ς↑) '()]
               [ς↓s : (Listof -ς↓) '()]
               [ς!s : (Listof -ς!) '()])
              ([ς (in-set ςs)])
      (cond [(-ς↑? ς) (values (cons ς ς↑s) ς↓s ς!s)]
            [(-ς↓? ς) (values ς↑s (cons ς ς↓s) ς!s)]
            [else     (values ς↑s ς↓s (cons (assert ς -ς!?) ς!s))])))
  )

(define-compound-unit/infer reduction@
  (import ast-pretty-print^ static-info^ meta-functions^ sat-result^
          prims^ proof-system^ local-prover^ widening^ verifier^
          for-gc^ val^ env^ sto^ path^ instr^ pretty-print^ prim-runtime^ summ^)
  (export reduction^ app^ mon^ kont^ compile^ havoc^)
  (link debugging@ memoize@ kont@ compile@ havoc@ mon@ fc@ app@ pre-reduction@))
