#lang typed/racket/base

(provide run-file havoc-file run-e run)

(require
 racket/match racket/set
 "../utils/main.rkt"
 "../ast/main.rkt"
 "../parse/main.rkt"
 "../runtime/main.rkt"
 (only-in "../proof-relation/main.rkt" φs⊢ₑₓₜe)
 (only-in "../proof-relation/ext/z3.rkt" z3⊢)
 "step.rkt"
 "init.rkt")

(: run-file : Path-String → (Values (℘ -A) #|debugging|# -M -Ξ))
(define (run-file p)
  (define m (file->module p))
  (define-values (σ₁ _) (𝑰 (list m)))
  (define-values (As M Ξ σ) (run (⇓ₘ m) σ₁))
  (values As M Ξ))

(: havoc-file : Path-String → (Values (℘ -A) #|debugging|# -M -Ξ))
(define (havoc-file p)
  (define m (file->module p))
  (define-values (σ₁ e₁) (𝑰 (list m)))
  (define-values (As M Ξ σ) (run (⇓ₚ (list m) e₁) σ₁))
  #;(begin
    (define best (extract-best))
    (printf "~a out of ~a:~n" (length best) (length data))
    (for ([(p i) (in-indexed best)])
      (match-define (cons (list _ (? -Γ? Γ) (? -e? s) R) t) p)
      (match-define (-Γ φs _ γs) Γ)
      (printf "~ntime: ~a ms~n" t)
      (for ([φ φs]) (printf "~a~n" (show-φ φ)))
      (for ([γ γs])
        (match-define (-γ τ bnd blm?) γ)
        (printf "~n~a | ~a~n" (show-binding bnd) (if blm? "(blame)" "(result)"))
        (for ([A (hash-ref M τ)])
          (match* (blm? A)
            [(#f (-ΓW Γ W))
             (printf "  - ~a~n" (show-A A))]
            [(_  (-ΓE Γ blm))
             (printf "  - ~a~n" (show-A A))])))
      (printf "-----------------------------------------~n")
      (printf "~a : ~a~n~n" (show-e s) R)))
  (values As M Ξ))

(: run-e : -e → (Values (℘ -A) #|for debugging|# -M -Ξ))
(define (run-e e)
  (define-values (σ₀ _) (𝑰 '()))
  (define-values (As M Ξ σ) (run (⇓ 'top e) σ₀))
  (values As M Ξ))


(define count : Natural 0)
(: run : -⟦e⟧ -σ → (Values (℘ -A) #|for debugging|# -M -Ξ -σ))
;; Run compiled program on initial heap
(define (run ⟦e⟧₀ σ₀)
  (define-type Seen-τ (HashTable -τ -σ))
  (define-type Seen-Co (HashTable (List -ℛ -τ -A) -M))
  ;(define-type Seen-Table (HashTable (U -τ (List -ℛ -τ -A)) (List -M #;-Ξ -σ)))
  
  (: loop : Seen-τ Seen-Co (℘ -τ) (℘ -Co) -M -Ξ -σ → (Values -M -Ξ -σ))
  (define (loop seen-τs seen-Cos τs Cos M Ξ σ)
    
    (cond
      [(and (set-empty? τs) (set-empty? Cos))
       (values M Ξ σ)]
      [else
       
       (begin ;; Pre-iter debuggings
         (define last : Integer (current-seconds))
         (set! count (+ 1 count))
         (define num-τs (set-count τs))
         (define num-Cos (set-count Cos))
         (printf "iter ~a: ~a (~a + ~a)~n" count (+ num-τs num-Cos) num-τs num-Cos)
         #;(begin ; verbose
           (printf "~a τs:~n" num-τs)
           (define τs-list (set->list τs))
           (define Cos-list (set->list Cos))
           (for ([(τ i) (in-indexed τs-list)])
             (printf "  -~a ~a~n" (n-sub i) (parameterize ([verbose? #t]) (show-τ τ))))
           (printf "~a Cos:~n" num-Cos)
           (for ([(Co i) (in-indexed Cos-list)])
             (printf "  -~a ~a~n" (n-sub (+ i num-τs)) (show-Co Co)))))

       ;; Widen global tables
       (define-values (δM δΞ δσ) (⊔³ (ev* M Ξ σ τs) (co* M Ξ σ Cos)))
       (define-values (M* Ξ* σ*) (⊔³ (values M Ξ σ) (values δM δΞ δσ)))

       ;; Check for un-explored execution of function bodies (≃ ⟨e, ρ, σ⟩)
       (define-values (τs* seen-τs*)
         (for/fold ([τs* : (℘ -τ) ∅] [seen-τs* : Seen-τ seen-τs])
                   ([τ (in-hash-keys δΞ)] #:unless (equal? (hash-ref seen-τs τ #f) σ*))
           (values (set-add τs* τ) (hash-set seen-τs* τ σ*))))

       ;; Check for un-explored returns
       (define-values (Cos* seen-Cos*)
         (let ([!Cos : (℘ -Co) ∅]
               [!seen-Cos : Seen-Co seen-Cos])

           (define (Γ->τs [Γ : -Γ]) : (℘ -τ)
             (match-define (-Γ _ _ γs) Γ)
             (for/set: : (℘ -τ) ([γ γs])
               (-γ-callee γ)))

           (: with-ret! : -ℛ -τ (℘ -A) → Void)
           ;; Update next returns to resume and seen nodes (imperatively)
           (define (with-ret! ℛ τ As)

             ;; Compute relevant part of memo table
             (define caller-τs
               (match-let ([(-ℛ τ (-ℋ (-ℒ _ Γ _) _ _)) ℛ])
                 (set-add (Γ->τs Γ) τ)))

             (define As*
               (for*/set: : (℘ -A) ([A As]
                                    [k (in-value (list ℛ τ A))]
                                    [callee-τs
                                     (in-value
                                      (match A
                                        [(-ΓW Γ _) (set-add (Γ->τs Γ) τ)]
                                        [(-ΓE Γ _) (set-add (Γ->τs Γ) τ)]))]
                                    [M** (in-value (m↓ M* (∪ caller-τs callee-τs)))]
                                    #:unless (equal? (hash-ref !seen-Cos k #f) M**)
                                    )
                 (set! !seen-Cos (hash-set !seen-Cos k M**))
                 A))
             (unless (set-empty? As*)
               (set! !Cos (set-add !Cos (-Co ℛ τ As*)))))

           ;; Plug each new result into known return edges
           (for* ([(τ As) (in-hash δM)] #:unless (set-empty? As)
                  [ℛ (in-set (Ξ@ Ξ* τ))])
             (with-ret! ℛ τ As))
           ;; Plug known result into each new return edge
           (for* ([(τ ℛs) (in-hash δΞ)]
                  [As (in-value (M@ M* τ))] #:unless (set-empty? As)
                  [ℛ (in-set ℛs)])
             (with-ret! ℛ τ As))

           (values !Cos !seen-Cos)))

       ;; Post-iter Debugging
       (parameterize ([verbose? #t])

         (: show-m (∀ (X Y) ([Sexp (X → Sexp) (Y → Sexp) (MMap X Y)]
                             [#:filter (X → Boolean)]
                             . ->* . Void)))
         (define (show-m l show-x show-y m #:filter [show-x? (λ (_) #t)])
           (printf "~a:~n" l)
           (for ([(x ys) m] #:when (show-x? x))
             (define n (set-count ys))
             (printf "  - ~a~n" (show-x x))
             (for ([(y i) (in-indexed ys)])
               (printf "      ↦~a~a ~a~n" (n-sup (add1 i)) (n-sub n) (show-y y)))))

         ;((inst show-m -α -V) 'δσ show-α show-V δσ #:filter (λ (α) (not (or (-α.def? α) (-α.wrp? α) (-e? α)))))
         ;((inst show-m -τ -A) 'δM show-τ show-A δM)
         ;((inst show-m -τ -ℛ) 'δΞ show-τ show-ℛ δΞ)
         (let* ([now (current-seconds)]
                [δ (- now last)])
           (set! last now)
           (printf "time: ~as~n" δ))
         #;(match (read) ; interactive
           ['done (error "done")]
           [(? exact-nonnegative-integer? i)
            (cond [(<= 0 i (sub1 num-τs))
                   (set! τs {set (list-ref τs-list i)})
                   (set! Cos ∅)]
                  [else
                   (set! τs ∅)
                   (set! Cos {set (list-ref Cos-list (- i num-τs))})])]
           [else (void)])
         (printf "~n"))
       
       (loop seen-τs* seen-Cos* τs* Cos* M* Ξ* σ*)]))

  (define τ₀ (-ℬ ⟦e⟧₀ ℒ∅))
  (define-values (M Ξ σ)
    (parameterize ([φs⊢ₑₓₜe z3⊢])
      (loop (hash τ₀ σ₀) (hash) {set τ₀} ∅ ⊥M ⊥Ξ σ₀)))
  (values (M@ M τ₀) M Ξ σ))

