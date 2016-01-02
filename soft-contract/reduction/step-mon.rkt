#lang typed/racket/base

(require
 racket/match racket/set racket/list
 "../utils/non-det.rkt" "../utils/set.rkt"
 "../ast/definition.rkt" "../ast/meta-functions.rkt"
 "../runtime/val.rkt" "../runtime/store.rkt" "../runtime/simp.rkt" "../runtime/addr.rkt"
 "../runtime/env.rkt" "../runtime/path-inv.rkt" "../runtime/summ.rkt" "../runtime/arity.rkt"
 "../proof-relation/main.rkt"
 "../machine/definition.rkt")

(provide ↦mon)

(: ↦mon : -WV -WV -Γ -κ -σ -Ξ -M Mon-Info Integer → -Δς*)
;; Stepping rules for contract monitoring
(define (↦mon W_c W_v Γ κ σ Ξ M l³ pos)
  (match-define (-W C e_c) W_c)
  (match-define (-W V e_v) W_v)
  (match-define (list l+ l- lo) l³)

  (: blm : Mon-Party Mon-Party -V -V → (-Γ → -Δς))
  (define ((blm l+ lo C V) Γ)
    (-Δς (-blm l+ lo C (list V)) Γ κ '() '() '()))

  (: ↦and/c : -α -α → -Δς*)
  (define (↦and/c γ₁ γ₂)
    (define Cs₁ (σ@ σ γ₁))
    (define Cs₂ (σ@ σ γ₂))
    (match-define (list c₁ c₂) (-app-split e_c 'and/c 2))
    (match/nd: (-V → -Δς) Cs₁
      [C₁
       (match/nd: (-V → -Δς) Cs₂
         [C₂
          (define κ* (-kont (-φ.mon.v (-W C₂ c₂) l³ pos) κ))
          (define W_c₁ (-W C₁ c₁))
          (↦mon W_c₁ W_v Γ κ* σ Ξ M l³ pos)])]))

  (: ↦or/c : -α -α → -Δς*)
  (define (↦or/c γ₁ γ₂)
    (define Cs₁ (σ@ σ γ₁))
    (define Cs₂ (σ@ σ γ₂))
    (match-define (list c₁ c₂) (-app-split e_c 'or/c 2))

    (match/nd: (-V → -Δς) Cs₁
      [C₁
       (define W_C₁ (-W C₁ c₁))
       (cond
         [(C-flat? C₁)
          (match/nd: (-V → -Δς) Cs₂
            [C₂
             (define κ* (-kont (-φ.if (-W (list V) e_v) (-Mon (-W C₂ c₂) W_v l³ pos)) κ))
             (define E* (-App W_C₁ (list W_v) (-src-loc lo pos)))
             (-Δς E* Γ κ* '() '() '())])]
         [else ;; C₁ is chaperone
          (match/nd: (-V → -Δς) Cs₂
            [C₂
             (define W_C₂ (-W C₂ c₂))
             (cond
               [(C-flat? C₂)
                (define κ* (-kont (-φ.if (-W (list V) e_v) (-Mon W_C₁ W_v l³ pos)) κ))
                (define E* (-App W_C₂ (list W_v) (-src-loc lo pos)))
                (-Δς E* Γ κ* '() '() '())]
               [else ; Both C₁ and C₂ are chaperones
                (define κ*
                  (-kont*
                   (-φ.filter-fo (list W_C₂) '() W_C₁ W_v l³ pos)
                   (-φ.@ '() (list W_C₁ -contract-first-order-passes?/W) (-src-loc lo pos))
                   κ))
                (-Δς (-W (list V) e_v) Γ κ* '() '() '())])])])]))

  (: ↦not/c : -α → -Δς*)
  (define (↦not/c α)
    (match/nd: (-V → -Δς) (σ@ σ α)
      [C*
       (cond 
         [(C-flat? C*)
          (match-define (list e_c*) (-app-split e_c 'not/c 1))
          (define κ* (-kont (-φ.if (-blm l+ lo C (list V)) (-W (list V) e_v)) κ))
          (-Δς (-App (-W C* e_c*) (list W_v) (-src-loc lo pos)) Γ κ* '() '() '())]
         [else
          ((blm lo 'Λ #|hack|#
                (-st-p (-struct-info (-id 'flat-contract? 'Λ) 1 ∅)) C*)
           Γ)])]))

  (: ↦=>i : -=>i → -Δς*)
  (define (↦=>i C)
    (match-define (-=>i Doms Rst d ρ_d Γ_d) C)
    (define n (length Doms))
    (define -bn (-b (if Rst (arity-at-least n) n)))
    (define-values (δς-ok δς-bads)
      (Γ+/- M σ Γ
            (λ ([Γ-ok : -Γ])
              (define α ((mk-α.fld) (list (-id 'Ar 'Λ) pos 0)))
              (define ?e (and e_v (closed? e_v) e_v))
              (define Ar (-Ar C (cons α ?e) l³))
              (define δσ (list (cons α V)))
              (-Δς (-W (list Ar) ?e) Γ-ok κ δσ '() '()))
            (list -procedure?/W (list W_v) (blm l+ lo 'procedure? V))
            (list -arity-includes?/W
                  (list W_v (-W -bn -bn))
                  (blm l+ lo (-Arity-Includes/C n) V))))
    (collect δς-ok δς-bads))
  
  (: ↦struct/c : -struct-info (Listof -α.struct/c) → -Δς*)
  (define (↦struct/c s γs)
    (define k? (-st-p s))
    (define k (-st-mk s))
    (define-values (Γ-ok Γ-bad) (Γ+/-W∋Ws M σ Γ (-W k? k?) W_v))

    ;; If struct tag does not match, blame right away
    (define ς-bad (and Γ-bad ((blm l+ lo k? V) Γ-bad)))

    ;; If struct tag matches, monitor each field
    ;; in addition to wrapping mutable field with contract
    (define ς-ok
      (and Γ-ok
           (match γs
             ['() (-Δς (-W (list (-St s '())) (-?@ k)) Γ-ok κ '() '() '())]
             [(cons γ γs*)
              (match-define (cons e_ci e_cs) (-struct/c-split e_c (length γs)))
              (define φ₁ (-φ.mon.struct s γs e_cs 0 '() W_v l³ pos))
              (define φ₃ (-φ.@ '() (list (-W (-st-ac s 0) #f)) (-src-loc 'Λ pos)))
              (for/set: : (Setof -Δς) ([C (σ@ σ γ)])
                (define φ₂ (-φ.mon.v (-W C e_ci) l³ pos))
                (define κ* (-kont* φ₃ φ₂ φ₁ κ))
                (-Δς (-W (list V) e_v) Γ-ok κ* '() '() '()))])))
    
    (collect ς-ok ς-bad))

  (: ↦vectorof : -α.vectorof → -Δς*)
  (define (↦vectorof α)
    (define-values (Γ-ok Γ-bad) (Γ+/-W∋Ws M σ Γ -vector?/W W_v))

    (define-values (δς-ok δς-bad)
      (Γ+/- M σ Γ
            (λ ([Γ-ok : -Γ])
              (define n : (Option Integer)
                (match V
                  [(-Vector αs) (length αs)]
                  [(-Vector/checked γs _ _) (length γs)]
                  [_ (match (-?@ 'vector-length e_v)
                       [(-b (? exact-integer? n)) n]
                       [_ #f])]))
              (cond
                [n =>
                 (λ ([n : Integer])
                   (for/set: : (Setof -Δς) ([C (σ@ σ α)])
                     (define W-c (-W C #f #|TODO|#))
                     (define φ-chk-rest (-φ.mon.vectorof (cons α W-c) n 1 (-W V e_v) l³ pos))
                     (define φ-chk-val (-φ.mon.v W-c l³ pos))
                     (define φ-ref (-φ.@ '() (list W_v -vector-ref/W) -Λ))
                     (define κ* (-kont* φ-ref φ-chk-val φ-chk-rest κ))
                     (-Δς (-W (list (-b 0)) (-b 0)) Γ-ok κ* '() '() '())))]
                [else
                 ;; Reference with opaque index and monitor.
                 ;; This is not really sound if vector contains thunks with side effects.
                 (for/set: : (Setof -Δς) ([C (σ@ σ α)])
                   (define φ-chk-val (-φ.mon.v (-W C #f #|TODO|#) l³ pos))
                   (define φ-ref (-φ.@ '() (list W_v -vector-ref/W) -Λ))
                   (define κ* (-kont* φ-ref φ-chk-val κ))
                   (-Δς (-W -●/Vs #f) Γ-ok κ* '() '() '()))]))
            (list -vector?/W (list W_v) (blm l+ lo 'vector? V)))) 
    
    (collect δς-ok δς-bad))

  (: ↦vector/c : (Listof -α.vector/c) → -Δς*)
  (define (↦vector/c γs)
    (define n (length γs))
    (define -n/W (let ([v (-b n)]) (-W v v)))
    (define -len/W
      (-W (match V
            [(-Vector αs) (-b (length αs))]
            [(-Vector/checked γs _ _) (-b (length γs))]
            [else -●/V])
          (-?@ 'vector-length e_v)))
    (define e_cs (-app-split e_c 'vector/c n))
    
    (define-values (δς-ok δς-bads)
      (Γ+/- M σ Γ
            (λ ([Γ-ok : -Γ])
              (match γs
                ['() (-Δς (-W (list -Vector₀) (-?@ 'vector)) Γ-ok κ '() '() '())]
                [(cons γ _)
                 (match-define (cons e_c₀ e_cs*) e_cs)
                 (define φ-chk-rest (-φ.mon.vector/c γs e_cs* 0 W_v l³ pos))
                 (for/set: : (Setof -Δς) ([C (σ@ σ γ)])
                   (define φ-chk-val (-φ.mon.v (-W C e_c₀) l³ pos))
                   (define φ-ref (-φ.@ '() (list W_v -vector-ref/W) -Λ))
                   (define κ* (-kont* φ-ref φ-chk-val φ-chk-rest κ))
                   (-Δς (-W (list (-b 0)) (-b 0)) Γ-ok κ* '() '() '()))]))
            (list -vector?/W (list W_v) (blm l+ lo 'vector? V))
            (list -=/W (list -n/W -len/W)
                  (blm l+ lo
                       (-Clo '(x)
                             (assert (-?@ '= (-?@ 'vector-length (-x 'x)) (-b n)))
                             -ρ⊥ -Γ⊤)
                       V))))

    (collect δς-ok δς-bads))

  (case (MσΓ⊢V∈C M σ Γ W_v W_c)
    [(✓)
     (define Γ* (Γ+ Γ (-?@ e_c e_v)))
     (-Δς (-W (list V) e_v) Γ* κ '() '() '())]
    [(X)
     (define Γ* (Γ+ Γ (-not (-?@ e_c e_v))))
     (-Δς (-blm l+ lo C (list V)) Γ* κ '() '() '())]
    [(?)
     (match C
       [(? -=>i?) (↦=>i C)]
       [(-St/C _ s γs) (↦struct/c s γs)]
       [(-x/C α)
        (match/nd: (-V → -Δς) (σ@ σ α)
          [C* (↦mon (-W C* (-x/c (-α.x/c-pos α))) W_v Γ κ σ Ξ M l³ pos)])]
       [(-And/C _ γ₁ γ₂) (↦and/c γ₁ γ₂)]
       [(-Or/C  _ γ₁ γ₂) (↦or/c  γ₁ γ₂)]
       [(-Not/C α) (↦not/c α)]
       [(-Vectorof α) (↦vectorof α)]
       [(-Vector/C αs) (↦vector/c αs)]
       [_
        (define κ* (-kont (-φ.if (-W (list V) e_v) (-blm l+ lo C (list V))) κ))
        (-Δς (-W (list V) e_v) Γ
             (-kont (-φ.@ '() (list W_c) (-src-loc lo pos)) κ*) '() '() '())])]))
