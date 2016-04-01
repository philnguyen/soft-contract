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
  (with-debugging/off
    ((ans)
     (for/fold ([ps : (℘ (Pairof -Γ (HashTable -e -e))) {set (cons Γ m∅)}])
               ([γ γs])
       (for/union : (℘ (Pairof -Γ (HashTable -e -e))) ([p ps])
         (match-define (cons Γ₀ m₀) p)
         (map/set
          (λ ([p : (Pairof -Γ (HashTable -e -e))])
            (match-define (cons Γ m) p)
            (cons Γ (hash-merge m₀ m)))
          (invert-γ M Γ₀ γ #;((γ/ m₀) γ))))))
    (printf "Invert ~a into:~n" (show-Γ Γ))
    (for ([p ans])
      (match-define (cons Γ m) p)
      (define-values (sΓ sγs) (show-M-Γ M Γ))
      (printf "  - ~a @ ~a~n"
              sΓ
              (for/list : (Listof Sexp) ([(x y) m])
                `(,(show-e x) ↦ ,(show-e y))))
      (for ([s sγs]) (printf "    + ~a~n" s)))
    (printf "~n")))

(: invert-γ : -M -Γ -γ → (℘ (Pairof -Γ (HashTable -e -e))))
;; Invert "hypothesis" `γ` in path-condition `Γ`.
;; May return multiple (refined) path-conditions due to imprecision
(define (invert-γ M Γ γ)
  (match-define (-Γ φs as γs) Γ)
  ; (assert (∋ γs γ)) Not that important as long as `invert-γ` is private
  (match-define (-γ τ bnd blm) γ)
  (define h∅ : (HashTable -e -e) (hash))
  (define m₀ (bnds->subst bnd))
  
  (define xs (-binding-dom bnd))

  (with-debugging/off
    ((ans)
     (for/fold ([ps : (℘ (Pairof -Γ (HashTable -e -e))) ∅])
               ([A (M@ M τ)])
       (match* (A blm) ; FIXME duplicate code
         [((-ΓW Γ₀ (-W Vs sₐ)) #f)
          (define-values (mₑₑ mₑᵣ _) (mk-subst m₀ bnd sₐ))
          (define Γₑᵣ₊ (ensure-simple-consistency (Γ/ mₑₑ (Γ↓ Γ₀ xs))))
          (define Γₑᵣ  (ensure-simple-consistency (Γ/ mₑᵣ (-Γ-minus-γ Γ γ))))
          (define Γ* (and Γₑᵣ₊ Γₑᵣ (Γ⊓ Γₑᵣ Γₑᵣ₊)))
          (if Γ* (set-add ps (cons Γ* mₑᵣ)) ps)]
         [((-ΓE Γ₀ (-blm l+ lo _ _)) (cons l+ lo))
          (define-values (mₑₑ mₑᵣ _) (mk-subst m₀ bnd #f))
          (define Γₑᵣ₊ (ensure-simple-consistency (Γ/ mₑₑ (Γ↓ Γ₀ xs))))
          (define Γₑᵣ  (ensure-simple-consistency (Γ/ mₑᵣ (-Γ-minus-γ Γ γ))))
          (define Γ* (and Γₑᵣ Γₑᵣ₊ (Γ⊓ Γₑᵣ Γₑᵣ₊)))
          (if Γ* (set-add ps (cons Γ* mₑᵣ)) ps)]
         [(_ _) ps])))
    (define-values (sΓ sγs) (show-M-Γ M Γ))
    (printf "Invert ~a at ~a, dom: ~a, where:~n" sΓ (show-γ γ) (set->list xs))
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

(: bnds->subst : -binding → (HashTable -e -e))
;; Convert list of `param -> arg` to hashtable
(define (bnds->subst bnd)
  (match-define (-binding _ _ x->e) bnd)
  (for*/hash : (HashTable -e -e) ([(x e) x->e])
    (values (-x x) e)))

(: mk-subst : (HashTable -e -e) -binding -s → (Values (HashTable -e -e) (HashTable -e -e) -s))
;; Given caller's parameters and arguments and callee's result,
;; Create a substitution to convert callee's propositions to caller's propositions.
;; Return 2 maps: first map is for callee, second for caller, plus unfolding of result
(define (mk-subst m₀ bnd a)
  (match-define (-binding f xs x->e) bnd)
  (define args (-binding-args bnd))
  (define dom (-binding-dom bnd))
  (define fargs (apply -?@ f args))
  
  ;; Unfold caller's result to callee's result if callee's result is in terms
  ;; of only variables caller understands
  (define fargs*
    (let ([all-args? (andmap (inst values Any) args)]
          [a* (s↓ a dom)])
      (and all-args? a* ((e/map m₀) a*))))
  
  (define sₐ (or fargs* fargs))

  (cond
    [(and a fargs fargs*)
     (values (hash-set m₀ a fargs*) (hash fargs fargs*) sₐ)]
    [(and a fargs)
     (values (hash-set m₀ a fargs ) (hash) sₐ)]
    [else (values m₀ (hash) sₐ)]))
