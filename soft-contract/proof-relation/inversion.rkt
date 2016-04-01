#lang typed/racket/base

(provide invert-ps invert-Γ bnds->subst mk-subst)

(require racket/match
         racket/set
         "../utils/main.rkt"
         "../ast/main.rkt"
         "../runtime/main.rkt"
         "local.rkt")

(: invert-ps : -M (℘ (Pairof -Γ -s)) → (℘ (Pairof -Γ -s)))
;; Invert path-condition `Γ` and rewrite symbolic value `s` accordingly
(define (invert-ps M ps)
  (with-debugging/off
    ((ans)
     (for/union : (℘ (Pairof -Γ -s)) ([p ps])
       (match-define (cons Γ s) p)
       (for/set: : (℘ (Pairof -Γ -s)) ([Γ-m (invert-Γ M Γ)])
         (match-define (cons Γ* m) Γ-m)
         (define s* (and s ((e/map* m) s)))
         #;(begin
             (printf "map:~n")
             (for ([(x y) m])
               (printf "  ~a ↦ ~a~n" (show-e x) (show-e y)))
             (printf "applied: ~a ↦ ~a~n" (show-s s) (show-s s*))
             (printf "~n"))
         (cons Γ* s*))))
    (printf "Invert:~n")
    (for ([p ps])
      (match-define (cons Γ s) p)
      (printf "  - ~a ⊢ ~a~n" (show-Γ Γ) (show-s s)))
    (printf "Into: ~n")
    (for ([p ans])
      (match-define (cons Γ s) p)
      (printf "  - ~a ⊢ ~a~n" (show-Γ Γ) (show-s s)))
    (printf "~n")))

(: invert-Γ : -M -Γ → (℘ (Pairof -Γ (HashTable -e -e))))
;; Invert all tails in path condition, accumulating substitutions that (heuristically)
;; should also be applied to unfold expressions into a more provable form.
;; This does not invert new tails added as a result of inverting existing ones.
(define (invert-Γ M Γ)
  (match-define (-Γ _ _ γs) Γ)
  (define m∅ : (HashTable -e -e) (hash))
  (for/fold ([ps : (℘ (Pairof -Γ (HashTable -e -e))) {set (cons Γ m∅)}])
            ([γ γs])
    (for/union : (℘ (Pairof -Γ (HashTable -e -e))) ([p ps])
       (match-define (cons Γ₀ m₀) p)
       (map/set
        (λ ([p : (Pairof -Γ (HashTable -e -e))])
          (match-define (cons Γ m) p)
          (cons Γ (hash-merge m₀ m)))
        (invert-γ M Γ₀ ((γ/ m₀) γ))))))

(: invert-γ : -M -Γ -γ → (℘ (Pairof -Γ (HashTable -e -e))))
;; Invert "hypothesis" `γ` in path-condition `Γ`.
;; May return multiple (refined) path-conditions due to imprecision
(define (invert-γ M Γ γ)
  (match-define (-Γ φs as γs) Γ)
  ; (assert (∋ γs γ)) Not that important as long as `invert-γ` is private
  (match-define (-γ τ sₕ bnds blm) γ)
  (define h∅ : (HashTable -e -e) (hash))
  (define m₀ (bnds->subst bnds))
  
  ;; If `sₕ` was created in caller's block,
  ;; its free variables and callers' free variables agree (assuming α-renaming)
  (define xs (set-add-list (fvₛ sₕ) (map (inst car Var-Name -s) bnds)))

  (with-debugging/off
    ((ans)
     (for/fold ([ps : (℘ (Pairof -Γ (HashTable -e -e))) ∅])
               ([A (M@ M τ)])
       (match* (A blm)
         [((-ΓW Γ₀ (-W Vs sₐ)) #f)
          (define-values (mₑₑ mₑᵣ _) (mk-subst m₀ sₕ bnds sₐ))
          (define Γ*
            (ensure-simple-consistency (Γ⊓ (Γ/ mₑᵣ (-Γ-minus-γ Γ γ))
                                           (Γ/ mₑₑ (Γ↓ Γ₀ xs)))))
          (if Γ* (set-add ps (cons Γ* mₑᵣ)) ps)]
         [((-ΓE Γ₀ (-blm l+ lo _ _)) (cons l+ lo))
          (define-values (mₑₑ mₑᵣ _) (mk-subst m₀ sₕ bnds #f))
          (define Γ*
            (ensure-simple-consistency (Γ⊓ (Γ/ mₑᵣ (-Γ-minus-γ Γ γ))
                                           (Γ/ mₑₑ (Γ↓ Γ₀ xs)))))
          (if Γ* (set-add ps (cons Γ* mₑᵣ)) ps)]
         [(_ _) ps])))
    (define-values (sΓ sγs) (show-M-Γ M Γ))
    (printf "Invert ~a at ~a, where:~n" sΓ (show-γ γ))
    (for ([s sγs]) (printf "  - ~a~n" s))
    (printf "Getting:~n")
    (for ([p ans])
      (match-define (cons Γ m) p)
      (printf "  - ~a with ~a~n"
              (show-Γ Γ)
              (for/list : (Listof Sexp) ([(x y) m])
                `(,(show-e x) ↦ ,(show-e y)))))
    (printf "~n")))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;; Helpers
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(: bnds->subst : (Listof (Pairof Var-Name -s)) → (HashTable -e -e))
;; Convert list of `param -> arg` to hashtable
(define (bnds->subst bnds)
  (for*/hash : (HashTable -e -e) ([bnd bnds]
                                  [s (in-value (cdr bnd))] #:when s
                                  [x (in-value (car bnd))])
    (values (-x x) s)))

(: mk-subst : (HashTable -e -e) -s (Listof (Pairof Var-Name -s)) -s
            → (Values (HashTable -e -e) (HashTable -e -e) -s))
;; Given caller's parameters and arguments and callee's result,
;; Create a substitution to convert callee's propositions to caller's propositions.
;; Return 2 maps: first map is for callee, second for caller, plus unfolding of result
(define (mk-subst m₀ f bnds a)
  (define-values (xs args) (unzip bnds))
  (define fvs (∪ (list->set xs) (fvₛ f)))

  ;; Caller's result as the function call
  (define fargs (apply -?@ f args))
  
  ;; Unfold caller's result to callee's result if callee's result is in terms
  ;; of only variables caller understands
  (define fargs*
    (let ([all-args? (andmap (inst values Any) args)]
          [a* (s↓ a fvs)])
      (and all-args? a* ((e/map m₀) a*))))
  
  (define sₐ (or fargs* fargs))

  (cond
    [(and a fargs fargs*)
     (values (hash-set m₀ a fargs*) (hash fargs fargs*) sₐ)]
    [(and a fargs)
     (values (hash-set m₀ a fargs ) (hash) sₐ)]
    [else (values m₀ (hash) sₐ)]))
