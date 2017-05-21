#lang typed/racket/base

(provide (except-out (all-defined-out) -not/c -not/c/simp)
         (rename-out [-not/c/simp -not/c]))

(require racket/match
         racket/set
         racket/string
         (except-in racket/list remove-duplicates)
         bnf
         intern
         set-extras
         "../utils/main.rkt"
         "../ast/main.rkt")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;; Environment
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define ⊥ρ : -ρ (hasheq))
(define (ρ@ [ρ : -ρ] [x : Symbol]) : ⟪α⟫
  (hash-ref ρ x (λ () (error 'ρ@ "~a not in environment ~a" x (hash-keys ρ)))))
(define ρ+ : (-ρ Symbol ⟪α⟫ → -ρ) hash-set)

;; HACK for distinguishing allocation contexts between 0-arg thunks,
;; which is important if the thunk returns different values (e.g. vector)
;; for different contexts
(define -x-dummy (+x! 'dummy))


(: )
(define (cardinality+ c)
  (case c
    [(0) 1]
    [(1) 'N]
    [else 'N]))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;; Stack Store
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define ⊥σₖ : -σₖ (hash))

(: σₖ@ : (U -Σ -σₖ) -αₖ → (℘ -κ))
(define (σₖ@ m αₖ)
  (hash-ref (if (-Σ? m) (-Σ-σₖ m) m) αₖ mk-∅))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;; Memo Table
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define ⊥M : -M (hash))

(: M@ : (U -Σ -M) -αₖ → (℘ -ΓA))
(define (M@ m αₖ) (hash-ref (if (-Σ? m) (-Σ-M m) m) αₖ mk-∅))



(define (W¹->W [W : -W¹])
  (match-define (-W¹ V s) W)
  (-W (list V) s))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;; Path condition
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; First order term for use in path-condition


(: )
(define (h-unique? h)
  (with-debugging/off ((u?) (match h
    [(-ℬ xs _ ρ)
     (set-empty? (set-remove (set-subtract (list->seteq (hash-keys ρ))
                               (formals->names xs))
                             -x-dummy))]
    [_ #|be careful when I have new stuff|# #t]))
    (printf "h-unique? ~a : ~a~n" (show-h h) u?)))

(: )
;; Check if term definiltey stands for a unique value.
;; `#f` is a conservative result of "maybe no"
(define (t-unique? t)
  (match t
    [(or (? -x?) (? -𝒾?) (? -v?)) #t]
    [(-t.@ h ts)
     (and (h-unique? h) (andmap t-unique? ts))]))

(: )
(define (t-contains? t t*)
  (let go ([t : -t t])
    (match t
      [t #:when (equal? t t*) #t]
      [(-t.@ _ ts) (ormap go ts)]
      [_ #f])))

(: )
(define (t-contains-any? t ts)
  (let go ([t : -t t])
    (match t
      [t #:when (∋ ts t) #t]
      [(-t.@ _ ts) (ormap go ts)]
      [_ #f])))

(: )
(define has-abstraction?
  (match-lambda
    [(-t.@ h ts)
     (or (-αₖ? h) (ormap has-abstraction? ts))]
    [_ #f]))



(define ⊤Γ (-Γ ∅ (hasheq)))

(: )
(define (-Γ-with-aliases Γ x ?t)
  (if ?t
      (match-let ([(-Γ ts as) Γ])
        (-Γ ts (hash-set as x ?t)))
      Γ))

(-special-bin-o . ::= . '> '< '>= '<= '= 'equal? 'eqv? 'eq? #|made up|# '≢)

(: )
(define (bin-o->h o)
  (case o
    [(>) ->/c]
    [(<) -</c]
    [(>=) -≥/c]
    [(<=) -≤/c]
    [(= equal? eqv? eq?) -≡/c]
    [(≢) -≢/c]))

(: )
;; Returns o* such that (o l r) ↔ (o* r l)
(define (flip-bin-o o)
  (case o
    [(<) '>]
    [(>) '<]
    [(>=) '<=]
    [(<=) '>=]
    [else o]))

(: )
;; Returns o* such that (o l r) ↔ (not (o* l r))
(define (neg-bin-o o)
  (case o
    [(<) '>=]
    [(>) '<=]
    [(>=) '<]
    [(<=) '>]
    [(= equal? eqv? eq?) '≢]
    [(≢) 'equal?]))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;; Call history
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Encodes monitor + call site
(struct -ℒ ([mons : (℘ ℓ)] [app : ℓ]) #:transparent)

(: )
(define (unpack-ℒ ℒ)
  (define ℓ (-ℒ-app ℒ))
  (values ℓ (ℓ-src ℓ)))

(define (ℒ-with-mon [ℒ : -ℒ] [ℓ : ℓ])
  (match-define (-ℒ ℓs ℓₐ) ℒ)
  (-ℒ (set-add ℓs ℓ) ℓₐ))

(define (ℒ-with-l [ℒ : -ℒ] [l : -l])
  (match-define (-ℒ ℓs ℓₐ) ℒ)
  (match-define (loc _ line col id) (ℓ->loc ℓₐ))
  (-ℒ ℓs (loc->ℓ (loc l line col id))))

(define ℋ∅ : -ℋ '())

(: ℋ+ : -ℋ (U -edge -ℒ)  → -ℋ)
;; Add edge on top of call history.
;; If the target is already there, return the history chunk up to first time the target
;; is seen
(define (ℋ+ ℋ x)
  (define match? : ((U -edge -ℒ) → Boolean)
    (cond [(-ℒ? x) (λ (e) (equal? e x))]
          [(-edge? x)
           (define x.tgt (-edge-tgt x))
           (λ (e) (and (-edge? e) (eq? x.tgt (-edge-tgt e))))]))
  (define ?ℋ (memf match? ℋ))
  (if ?ℋ ?ℋ (cons x ℋ)))


;; The call history is passed around a lot and is part of address allocation
;; So it may be useful to intern for cheaper comparison
(define-interner -⟪ℋ⟫ -ℋ
  #:intern-function-name -ℋ->-⟪ℋ⟫
  #:unintern-function-name -⟪ℋ⟫->-ℋ)
(define ⟪ℋ⟫∅ (-ℋ->-⟪ℋ⟫ ℋ∅))

(: ⟪ℋ⟫+ : )
(define (⟪ℋ⟫+ ⟪ℋ⟫ e) (-ℋ->-⟪ℋ⟫ (ℋ+ (-⟪ℋ⟫->-ℋ ⟪ℋ⟫) e)))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;; Value address
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Some address values have `e` embeded in them.
;; This used to be a neccessary precision hack.
;; Nowaways it's just a temporary fix for the inaccurate source location returned
;; by `fake-contract`

(define ⟪α⟫ₕᵥ (-α->⟪α⟫ (-α.hv)))
(define ⟪α⟫ₒₚ (-α->⟪α⟫ (-α.fn.●)))

(define ⊥σ (-σ (hasheq ⟪α⟫ₕᵥ ∅) ∅eq (hasheq)))
(define (⊥Σ) (-Σ ⊥σ ⊥σₖ ⊥M))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;; Compiled expression
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Cache for address lookup in local block
;; TODO: merge this in as part of path-condition
(define $∅ : -$ (hash))
(define ($@ [$ : -$] [t : -?t]) : (Option -V)
  (and t (hash-ref $ t #f)))

(define ($+ [$ : -$] [t : -?t] [V : -V]) : -$
  (if t (hash-set $ t V) $))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;; Pretty printing
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;



