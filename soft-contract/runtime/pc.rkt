#lang typed/racket/base

(require typed/racket/unit
         racket/match
         racket/set
         set-extras
         "../utils/main.rkt"
         "../ast/main.rkt"
         "signatures.rkt")

(provide pc@)

(define-unit pc@
  (import env^)
  (export pc^)

  (: h-unique? : -h → Boolean)
  (define (h-unique? h)
    (with-debugging/off ((u?) (match h
                                [(-ℬ xs _ ρ)
                                 (set-empty? (set-remove (set-subtract (list->seteq (hash-keys ρ))
                                                                       (formals->names xs))
                                                         -x-dummy))]
                                [_ #|be careful when I have new stuff|# #t]))
      (printf "h-unique? ~a : ~a~n" (show-h h) u?)))

  (: t-unique? : -t → Boolean)
  ;; Check if term definiltey stands for a unique value.
  ;; `#f` is a conservative result of "maybe no"
  (define (t-unique? t)
    (match t
      [(or (? -x?) (? -𝒾?) (? -v?)) #t]
      [(-t.@ h ts)
       (and (h-unique? h) (andmap t-unique? ts))]))

  (: t-contains? : -t -t → Boolean)
  (define (t-contains? t t*)
    (let go ([t : -t t])
      (match t
        [t #:when (equal? t t*) #t]
        [(-t.@ _ ts) (ormap go ts)]
        [_ #f])))

  (: t-contains-any? : -t (℘ -t) → Boolean)
  (define (t-contains-any? t ts)
    (let go ([t : -t t])
      (match t
        [t #:when (∋ ts t) #t]
        [(-t.@ _ ts) (ormap go ts)]
        [_ #f])))

  (: has-abstraction? : -t → Boolean)
  (define has-abstraction?
    (match-lambda
      [(-t.@ h ts)
       (or (-αₖ? h) (ormap has-abstraction? ts))]
      [_ #f]))

  (define ⊤Γ (-Γ ∅ (hasheq)))

  (: -Γ-with-aliases : -Γ Symbol -?t → -Γ)
  (define (-Γ-with-aliases Γ x ?t)
    (if ?t
        (match-let ([(-Γ ts as) Γ])
          (-Γ ts (hash-set as x ?t)))
        Γ))

  (: bin-o->h : -special-bin-o → Base → -h)
  (define (bin-o->h o)
    (case o
      [(>) ->/c]
      [(<) -</c]
      [(>=) -≥/c]
      [(<=) -≤/c]
      [(= equal? eqv? eq?) -≡/c]
      [(≢) -≢/c]))

  (: flip-bin-o : -special-bin-o → -special-bin-o)
  ;; Returns o* such that (o l r) ↔ (o* r l)
  (define (flip-bin-o o)
    (case o
      [(<) '>]
      [(>) '<]
      [(>=) '<=]
      [(<=) '>=]
      [else o]))

  (: neg-bin-o : -special-bin-o → -special-bin-o)
  ;; Returns o* such that (o l r) ↔ (not (o* l r))
  (define (neg-bin-o o)
    (case o
      [(<) '>=]
      [(>) '<=]
      [(>=) '<]
      [(<=) '>]
      [(= equal? eqv? eq?) '≢]
      [(≢) 'equal?]))

  ;; Cache for address lookup in local block
;; TODO: merge this in as part of path-condition
  (define $∅ : -$ (hash))
  (define ($@ [$ : -$] [t : -?t]) : (Option -V)
    (and t (hash-ref $ t #f)))

  (define ($+ [$ : -$] [t : -?t] [V : -V]) : -$
    (if t (hash-set $ t V) $)))
