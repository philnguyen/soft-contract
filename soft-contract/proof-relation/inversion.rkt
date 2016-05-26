#lang typed/racket/base

(provide (struct-out -ctx) (struct-out -γʰ) Γ->ctx invert-ctx invert-ctxs 
         (struct-out -cfg) inj-cfg invert-cfg invert-cfgs
         bnds->subst mk-subst
         show-γʰ
         )

(require racket/match
         racket/set
         "../utils/main.rkt"
         "../ast/main.rkt"
         "../runtime/main.rkt"
         "local.rkt")


;; Path-condition tail tagged with inversion history (to recognize repeated unfoldings)
(struct -γʰ ([tail : -γ] [hist : (℘ -τ)]) #:transparent)
;; A proof context contains hypotheses, invertible hypotheses, and rewriting hints
(struct -ctx ([facts : (℘ -φ)] [tails : (Listof -γʰ)] [m : (HashTable -φ -φ)]) #:transparent)
;; Proof configuration is proof context paired with an expression (may or may not be a goal)
(struct -cfg ([ctx : -ctx] [expr : -e]) #:transparent)

(: inj-cfg : -Γ -e → -cfg)
;; Load initial proof configuration
(define (inj-cfg Γ e) (-cfg (Γ->ctx Γ) e))

(: Γ->ctx : -Γ → -ctx)
;; Convert path-condition into proof context (ready to be inverted when neccessary)
(define (Γ->ctx Γ)
  (match-define (-Γ φs _ γs) Γ)
  (define γʰs (for/list : (Listof -γʰ) ([γ γs]) (-γʰ γ ∅)))
  (-ctx φs γʰs m∅))

(: invert-cfgs : -M (℘ -cfg) → (℘ -cfg))
(define (invert-cfgs M cfgs)
  (for/union : (℘ -cfg) ([cfg cfgs]) (invert-cfg M cfg)))

(: invert-cfg : -M -cfg → (℘ -cfg))
;; Invert all tails in proof configuration,
;; returning possible configuration(s) resulting in the current one
;; E.g. if memo table M has full evaluation results of `list?`:
;;      ⟨{cons? y}; {list? x, list? y}; (equal? x y)⟩
;;      --> (SPURIOUS) ⟨{nil? x, nil? y, cons? y}; {}; (equal? x y)⟩
;;      --> ⟨{nil? x, cons? y}; {list? (cdr y)}; (equal? x y)⟩
;;      --> (SPURIOUS) ⟨{cons? x, nil? y ,cons? y}; {list? (cdr x)}; (equal? x y)⟩
;;      --> ⟨{cons? x, cons? y}; {list? (cdr x), list? (cdr y)}; (equal? x y)⟩
(define (invert-cfg M cfg)
  ;(define last (current-milliseconds))
  (with-debugging/off
    ((ans)
     (match-define (-cfg ctx e) cfg)
     ;; For each resulting inverted context, rewrite the expression accordingly
     (for/set: : (℘ -cfg) ([ctx* (invert-ctx M ctx)])
       (match-define (-ctx _ _ m) ctx*)
       (-cfg ctx* (e/map m e))))
    #;(when (> δ 1000)
      (define (printf-cfg [cfg : -cfg])
        (match-define (-cfg (-ctx φs γʰs m) e) cfg)
        (for ([φ φs])
          (printf "~a~n" (show-e φ)))
        (for ([γʰ γʰs])
          (printf "~a~n" (show-γʰ γʰ)))
        (for ([(x y) m])
          (printf "~a ↦ ~a~n" (show-e x) (show-e y)))
        (printf "-----------------------------------------~n")
        (printf "~a~n~n" (show-e e)))
      (printf-cfg cfg)
      (printf "Results in ~ams:~n" δ)
      (for ([(cfgᵢ i) (in-indexed ans)])
        (printf "~a:~n" i)
        (printf-cfg cfgᵢ)))))

(: invert-ctxs : -M (℘ -ctx) → (℘ -ctx))
(define (invert-ctxs M ctxs)
  (for/union : (℘ -ctx) ([ctx ctxs]) (invert-ctx M ctx)))

(: invert-ctx : -M -ctx → (℘ -ctx))
;; Invert all tails in proof context, returning possible context(s) resulting in current one
(define (invert-ctx M ctx)
  (match-define (-ctx φs γʰs m) ctx)
  (with-debugging/off
    ((ctxs)
     (define ctx₀ (-ctx φs '() m))
     (for/fold ([acc : (℘ -ctx) {set ctx₀}])
               ([γʰ (reverse γʰs)]) ; TODO: foldr or manual loop instead?
       (for/union : (℘ -ctx) ([ctxᵢ acc])
         (invert-γ M ctxᵢ γʰ))))
    (printf "invert-ctx: ~a, ~a~n" (set-map φs show-e) (map show-γʰ γʰs))
    (printf "mapping:~n")
    (for ([r (show-e-map m)])
      (printf "    + ~a~n" r))
    (printf "result:~n")
    (for ([ctx ctxs])
      (match-define (-ctx φs γʰs m) ctx)
      (printf "  - ~a, ~a~n" (set-map φs show-e) (map show-γʰ γʰs))
      (printf "    mapping:~n")
      (for ([r (show-e-map m)])
        (printf "    + ~a~n" r)))
    (printf "~n")))

(: invert-γ : -M -ctx -γʰ → (℘ -ctx))
;; Invert tail `γ` in proof context, returing possible contexts resulting in current one
(define (invert-γ M ctx γʰ)
  (match-define (-ctx φs γʰs m) ctx)
  (match-define (-γʰ γ τs) γʰ)
  (match-define (-γ τ bnd₀ blm) γ)
  (define bnd (binding/ m bnd₀))
  
  (with-debugging/off
    ((ctxs)
     (cond
       ;; Just stop here for now.
       ;; TODO: need more care for sound induction without accidentally admitting non-sense
       [(∋ τs τ)
        {set ctx}]
       ;; Invert for new hypotheses and tails
       [else
        (define m₀ (bnds->subst bnd))
        (define fvs (-binding-dom bnd))
        (define τs* (set-add τs τ))
        
        #;#;(: on-ans : (℘ -ctx) (℘ -e) (Listof -γ) -s → (℘ -ctx))
        ;; Return the case unless it's inconsistent
        (define (on-ans acc φsₑₑ γsₑₑ sₑₑ)
          (define-values (mₑₑ δmₑᵣ _) (mk-subst m₀ bnd sₑₑ))
          (define mₑᵣ (combine-e-map m δmₑᵣ))
          (define φsₑᵣ₊ (φs/ensure-consistency mₑₑ (φs↓ φsₑₑ fvs)))
          (define φsₑᵣ  (φs/ensure-consistency mₑᵣ φs))
          (define φs* (and φsₑᵣ φsₑᵣ₊ (es⊓ φsₑᵣ φsₑᵣ₊)))
          (define δγʰs
            (for/list : (Listof -γʰ) ([γₑₑ γsₑₑ])
              (define γₑᵣ ((γ/ mₑₑ) γₑₑ))
              (-γʰ γₑᵣ τs*)))
          (with-debugging/off
            ((ctxs)
             (cond
               [φs*
                (define ctx* (-ctx φs* (append δγʰs γʰs) mₑᵣ))
                (set-add acc ctx*)]
               [else acc]))
            (printf "on-ans:~n")
            (printf "  - callee knows: ~a~n" (set-map φsₑₑ show-e))
            (printf "  - calle res: ~a~n" (and sₑₑ (show-e sₑₑ)))
            (printf "  - caller addition: ~a~n" (and φsₑᵣ₊ (set-map φsₑᵣ₊ show-e)))
            (printf "  - caller final: ~a~n" (and φs* (set-map φs* show-e)))
            (printf "~n")))
        
        (define f-on-ans (on-ans m₀ bnd m fvs φs τs* γʰs))
        ;; For each observed result from memo table, unfold and accumulate the case
        ;; unless it's inconsistent
        (for/fold ([acc : (℘ -ctx) ∅])
                  ([A (M@ M τ)])
          (match* (A blm)
            [((-ΓW (-Γ φs₀ _ γs₀) (-W _ sₐ)) #f)
             (f-on-ans acc φs₀ γs₀ sₐ)]
            [((-ΓE (-Γ φs₀ _ γs₀) (-blm l+ lo _ _)) (cons l+ lo))
             (f-on-ans acc φs₀ γs₀ #f)]
            [(_ _) acc]))]))
    (parameterize ([verbose? #t])
      (when (>= (set-count ctxs) 20)
        (printf "invert-γ: ~a, ~a @ ~a~n" (set-map φs show-e) (map show-γʰ γʰs) (show-γʰ γʰ))
        (printf "mappings:~n")
        (for ([(x y) m]) (printf "    + ~a ↦ ~a~n" (show-e x) (show-e y)))
        (for ([ctx* ctxs])
          (match-define (-ctx φs γʰs m) ctx*)
          (printf "  - ~a, ~a~n" (set-map φs show-e) (map show-γʰ γʰs))
          (printf "    mapping:~n")
          (for ([r (show-e-map m)]) (printf "    + ~a~n" r)))
        (printf "~n")))))

;(: on-ans : (HashTable -φ -φ) -binding (HashTable -φ -φ) (℘ Var-Name) (℘ -e) (℘ -τ) (Listof -γʰ) #||# (℘ -ctx) (℘ -e) (Listof -γ) -s → (℘ -ctx))
;; Return the case unless it's inconsistent
;; [experiment] Lifted out and memoized
(define/memo (on-ans [m₀ : (HashTable -φ -φ)]
                     [bnd : -binding]
                     [m : (HashTable -φ -φ)]
                     [fvs : (℘ Var-Name)]
                     [φs : (℘ -φ)]
                     [τs* : (℘ -τ)]
                     [γʰs : (Listof -γʰ)])
             : ((℘ -ctx) (℘ -φ) (Listof -γ) -s → (℘ -ctx))

  (define/memo (f [acc : (℘ -ctx)]
                  [φsₑₑ : (℘ -φ)]
                  [γsₑₑ : (Listof -γ)]
                  [sₑₑ : -s]) : (℘ -ctx)
    (define-values (mₑₑ δmₑᵣ _) (mk-subst m₀ bnd sₑₑ))
    (define mₑᵣ (combine-e-map m δmₑᵣ))
    (define φsₑᵣ₊ (φs/ensure-consistency mₑₑ (φs↓ φsₑₑ fvs)))
    (define φsₑᵣ  (φs/ensure-consistency mₑᵣ φs))
    (define φs* (and φsₑᵣ φsₑᵣ₊ (φs⊓ φsₑᵣ φsₑᵣ₊)))
    (with-debugging/off
      ((ctxs)
       (cond
         [φs*
          (define δγʰs
            (for/list : (Listof -γʰ) ([γₑₑ γsₑₑ])
              (define γₑᵣ ((γ/ mₑₑ) γₑₑ))
              (-γʰ γₑᵣ τs*)))
          (define ctx* (-ctx φs* (append δγʰs γʰs) mₑᵣ))
          (set-add acc ctx*)]
         [else acc]))
      (printf "on-ans:~n")
      (printf "  - callee knows: ~a~n" (set-map φsₑₑ show-e))
      (printf "  - calle res: ~a~n" (and sₑₑ (show-e sₑₑ)))
      (printf "  - caller addition: ~a~n" (and φsₑᵣ₊ (set-map φsₑᵣ₊ show-e)))
      (printf "  - caller final: ~a~n" (and φs* (set-map φs* show-e)))
      (printf "~n")))
  f)


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;; Helpers
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(: combine-e-map : (HashTable -φ -φ) (HashTable -φ -φ) → (HashTable -φ -φ))
(define (combine-e-map m δm)
  (define δm*
    (for/hasheq : (HashTable -φ -φ) ([(x y) δm])
      (values (φ/map m x) (φ/map m y))))
  (e-map-union m δm*))

(: bnds->subst : -binding → (HashTable -φ -φ))
;; Convert list of `param -> arg` to hashtable
(define (bnds->subst bnd)
  (match-define (-binding _ _ x->φ) bnd)
  (for/hasheq : (HashTable -φ -φ) ([(x φ) x->φ])
    (values (e->φ (-x x)) φ)))

(: mk-subst : (HashTable -φ -φ) -binding -s → (Values (HashTable -φ -φ) (HashTable -φ -φ) -s))
;; Given caller's parameters and arguments and callee's result,
;; Create a substitution to convert callee's propositions to caller's propositions.
;; Return 2 maps: first map is for callee, second for caller, plus unfolding of result
(define (mk-subst m₀ bnd a)
  (match-define (-binding f xs x->φ) bnd)
  (define args : (Listof -s)
    (for/list ([x xs])
      (cond [(hash-ref x->φ x #f) => φ->e]
            [else #f])))
  (define dom (-binding-dom bnd))
  (define fargs (apply -?@ (and f (φ->e f)) args))
  (define-values (fargs↓ mₐ) (β* fargs))
  
  ;; Unfold caller's result to callee's result if callee's result is in terms
  ;; of only variables caller understands
  (define fargsₐ
    (let ([all-args? (andmap (inst values Any) args)]
          [a* (s↓ (and a (e/map mₐ a)) dom)])
      (and all-args? a* (e/map m₀ a*))))
  
  (with-debugging/off
    ((mₑₑ mₑᵣ sₐ)
     (cond
       [(and a fargs fargs↓ fargsₐ)
        (define ⦇fargsₐ⦈ (e->φ fargsₐ))
        (values (hash-set m₀ (e->φ a) ⦇fargsₐ⦈) (hasheq (e->φ fargs) ⦇fargsₐ⦈ (e->φ fargs↓) ⦇fargsₐ⦈) fargsₐ)]
       [(and a fargs fargs↓)
        (values (hash-set m₀ (e->φ a) (e->φ fargs↓)) m∅ fargs↓)]
       [else (values m₀ m∅ fargs↓)]))
    (printf "mk-subst:~n")
    (printf "  - m₀: ~a~n" (show-e-map m₀))
    (printf "  - bnd: ~a~n" (show-binding bnd))
    (printf "  - fvs: ~a~n" (set-map dom show-Var-Name))
    (printf "  - mₑₑ: ~a~n" (show-e-map mₑₑ))
    (printf "  - mₑᵣ: ~a~n" (show-e-map mₑᵣ))
    (printf "  - sₐ: ~a~n" (show-s sₐ))
    (printf "~n")))

(: β* : -s → (Values -s (HashTable -φ -φ)))
;; Take β-normal form. Assume the user of this function knows for sure it exists.
(define (β* s)
  (with-debugging/off
    ((sₐ mₐ)
     (define m : (HashTable -φ -φ) m∅)
     (: go! (case-> [#f → #f] [-e → -e] [-s → -s]))
     (define (go! s)
       (match s
         [(-@ f args _)
          (match* ((go! f) (map go! args))
            [((-λ (? list? xs) e) args*)
             (for ([x xs] [arg args*])
               (set! m (hash-set m (e->φ (-x x)) (e->φ arg))))
             (go! (e/map m e))]
            [(f* args*) (-@ f* args* 0)])]
         [_ s]))
     (define sₐ (go! s))
     (values sₐ m))
    (printf "β* ~a -> ~a, ~a~n"
            (show-s s)
            (show-s sₐ)
            (show-e-map mₐ))))

(define (show-γʰ [γʰ : -γʰ]) (show-γ (-γʰ-tail γʰ)))
