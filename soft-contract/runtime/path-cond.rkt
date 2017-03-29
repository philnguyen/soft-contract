#lang typed/racket/base

(provide (all-defined-out))

(require racket/match
         racket/set
         "../utils/main.rkt"
         "../ast/main.rkt"
         "definition.rkt"
         "simp.rkt")

(: fv-as : (HashTable Symbol -t) → (℘ Symbol))
(define (fv-as as)
  (for/unioneq : (℘ Symbol) ([(x t) (in-hash as)])
     (set-add (fvₜ t) x)))

(: fvₜ : -?t → (℘ Symbol))
(define (fvₜ t)
  (match t
    [(-t.@ h ts) (apply set-union ∅eq (map fvₜ ts))]
    [(? -e? e) (fv e)]
    [#f ∅eq]))

(define (?t↓ [?t : -?t] [xs : (℘ Symbol)]) (and ?t (t↓ ?t xs)))

(: t↓ : -t (℘ Symbol) → -?t)
(define (t↓ t xs)
  (and (not (set-empty? (∩ (fvₜ t) xs))) #;(⊆ (fv e) xs) t))

(: ts↓ : (℘ -t) (℘ Symbol) → (℘ -t))
(define (ts↓ ts xs)
  (for*/set: : (℘ -t) ([t ts]
                       [t* (in-value (t↓ t xs))] #:when t*)
     t*))

(: Γ↓ : -Γ (℘ Symbol) → -Γ)
;; Restrict path-condition to given free variables
(define (Γ↓ Γ xs)
  (match-define (-Γ φs as) Γ)
  (define φs* (ts↓ φs xs))
  (define as*
    (for/hasheq : (HashTable Symbol -t) ([(x t) as] #:when (∋ xs x))
      (values x t)))
  (-Γ φs* as*))

(: canonicalize : (U -Γ (HashTable Symbol -t)) Symbol → -t)
;; Return an expression canonicalizing given variable in terms of lexically farthest possible variable(s)
(define (canonicalize X x)
  (cond [(-Γ? X) (canonicalize (-Γ-aliases X) x)]
        [else (hash-ref X x (λ () (-x x)))]))

(: predicates-of : (U -Γ (℘ -t)) -?t → (℘ -h))
;; Extract predicates that hold on given symbol
(define (predicates-of Γ t)
  (cond
    [(-Γ? Γ) (predicates-of (-Γ-facts Γ) t)]
    [t
     ;; tmp hack for integer precision
     ;; TODO: these hacks will be obsolete when the `def-prim` DSL is generalized
     (define ps : (℘ -h)
       (match t
         [(-t.@ '+ (or (list t* (-b (and (? real?) (? positive?))))
                       (list (-b (and (? real?) (? positive?))) t*)))
          #:when (and t* (∋ Γ (-t.@ '<= (list -zero t*))))
          {set (->/c 0)}]
         [(-t.@ '- (list t₁ t₂))
          (cond [(or (∋ Γ (-t.@ '<= (list t₂ t₁)))
                     (∋ Γ (-t.@ '>= (list t₁ t₂))))
                 {set (-≥/c 0)}]
                [(or (∋ Γ (-t.@ '< (list t₂ t₁)))
                     (∋ Γ (-t.@ '> (list t₁ t₂))))
                 {set (->/c 0)}]
                [else ∅])]
         [(-t.@ '* (list t t))
          {set (-≥/c 0)}]
         [_ ∅]))
     (for/fold ([ps : (℘ -h) ps]) ([φ (in-set Γ)])
       (match φ
         ;; unary
         [(-t.@ 'negative? (list (== t))) (set-add ps (-</c 0))]
         [(-t.@ 'positive? (list (== t))) (set-add ps (->/c 0))]
         ;; binary
         [(-t.@ (? -special-bin-o? o) (list (== t) (-b b)))
          (set-add ps ((bin-o->h o) b))]
         [(-t.@ (? -special-bin-o? o) (list (-b b) (== t)))
          (set-add ps ((bin-o->h (flip-bin-o o)) b))]
         ;; negate unary
         [(-t.@ 'not (list (-t.@ (? -o? o) (list (== t)))))
          (set-add ps (-not/c o))]
         ;; negate binary
         [(-t.@ 'not (list (-t.@ (? -special-bin-o? o) (list (== t) (-b b)))))
          (set-add ps ((bin-o->h (neg-bin-o o)) b))]
         [(-t.@ 'not (list (-t.@ (? -special-bin-o? o) (list (-b b) (== t)))))
          (set-add ps ((bin-o->h (neg-bin-o (flip-bin-o o))) b))]
         ;; Keep anything purely syntactic
         [(-t.@ (? h-syntactic? h) (list (== t))) (set-add ps h)]
         [_ ps]))]
    [else ∅]))

(: h-syntactic? : -h → Boolean)
(define (h-syntactic? h) (not (-αₖ? h)))

(: complement? : -t -t → Boolean)
(define complement?
  (match-lambda**
   [(φ (-t.@ 'not (list φ))) #t]
   [((-t.@ 'not (list φ)) φ) #t]
   [((-t.@ '<  (list t₁ t₂))
     (-t.@ '<= (list t₂ t₁))) #t]
   [((-t.@ '<= (list t₂ t₁))
     (-t.@ '<  (list t₁ t₂))) #t]
   [(_ _) #f]))
