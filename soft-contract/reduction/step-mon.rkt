#lang typed/racket/base

(require
 racket/match racket/set racket/list
 "../utils.rkt" "../ast.rkt" "../runtime.rkt" "../provability.rkt" "../machine.rkt")

(provide ↦mon ↦FC)

(: ↦mon : -WV -WV -Γ -κ -σ -Ξ -M Mon-Info Integer → -Δς*)
;; Stepping rules for contract monitoring
(define (↦mon W_c W_v Γ κ σ Ξ M l³ pos)
  (match-define (-W C e_c) W_c)
  (match-define (-W V e_v) W_v)
  (match-define (list l+ l- lo) l³)

  (: ↦and/c : -α -α → -Δς*)
  (define (↦and/c γ₁ γ₂)
    (define Cs₁ (σ@ σ γ₁))
    (define Cs₂ (σ@ σ γ₂))
    (match-define (list c₁ c₂) (-struct-split e_c -s-and/c))
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
    (match-define (list c₁ c₂) (-struct-split e_c -s-or/c))
    (match/nd: (-V → -Δς) Cs₁
      [C₁
       (cond
         [(C-flat? σ C₁)
          (match/nd: (-V → -Δς) Cs₂
            [C₂
             (define κ* (-kont (-φ.if (-Mon (-W C₂ c₂) W_v l³ pos)
                                      (-blm l+ lo C₁ (list V)))
                               κ))
             (define E* (-FC (-W C₁ c₁) W_v lo pos))
             (-Δς E* Γ κ* '() '() '())])]
         [else
          (-Δς (-blm lo 'Λ #|hack|#
                     (-st-p (-struct-info (-id-local 'flat-contract? 'Λ) 1 ∅)) (list C₁))
               Γ κ '() '() '())])]))

  (: ↦not/c : -α → -Δς*)
  (define (↦not/c α)
    (match/nd: (-V → -Δς) (σ@ σ α)
      [C*
       (cond
         [(C-flat? σ C*)
          (match-define (list e_c*) (-struct-split e_c -s-not/c))
          (define κ* (-kont (-φ.if (-blm l+ lo C (list V)) (-W (list V) e_v)) κ))
          (-Δς (-FC (-W C* e_c*) W_v lo pos) Γ κ* '() '() '())]
         [else
          (-Δς (-blm lo 'Λ #|hack|#
                     (-st-p (-struct-info (-id-local 'flat-contract? 'Λ) 1 ∅)) (list C*))
               Γ κ '() '() '())])]))

  (: ↦=>i : (Listof Symbol) (Listof -?e) (Listof -α) -e -ρ -Γ → -Δς*)
  (define (↦=>i xs cs Cs d ρ_d Γ_d)
    ;; TODO: check for arity also
    (define-values (Γ-ok Γ-bad) (Γ+/-W∈W M σ Γ W_v (-W 'procedure? 'procedure?)))
    (define ς-ok
      (and Γ-ok
           (let ()
             (define α
               (cond [e_v (-α.tmp e_v)]
                     [else (-α.fld (-id-local 'Ar 'Λ) pos 0)]))
             (define Ar (-Ar xs cs Cs d ρ_d Γ_d α l³))
             (define δσ (list (cons α V)))
             (-Δς (-W (list Ar) e_v #|TODO|#) Γ-ok κ δσ '() '()))))
    (define ς-bad
      (and Γ-bad
           (-Δς (-blm l+ lo 'procedure? (list V)) Γ-bad κ '() '() '())))
    (cond
      [(and ς-ok ς-bad) {set ς-ok ς-bad}]
      [ς-ok ς-ok]
      [else (assert ς-bad)]))
  
  (: ↦struct/c : -struct-info (Listof -α) → -Δς*)
  (define (↦struct/c s γs)
    (define k? (-st-p s))
    (define k (-st-mk s))
    (define-values (Γ-ok Γ-bad) (Γ+/-W∈W M σ Γ W_v (-W k? k?)))

    ;; If struct tag does not match, blame right away
    (define ς-bad
      (and Γ-bad (-Δς (-blm l+ lo k? (list V)) Γ-bad κ '() '() '())))

    ;; If struct tag matches, monitor each field
    ;; in addition to wrapping mutable field with contract
    (define ς-ok
      (and Γ-ok
           (let ()
             (match-define (-struct-info _ n mutables) s)
             (define e_ctcs (-struct/c-split e_c n))
             (define e_flds (-struct-split   e_v s))

             ;; look up possible field and contract lists
             ;; TODO: this can explode fast. Delay?
             (define fld-lsts : (Setof (Listof -V))
               (match V
                 [(-St _ αs) (σ@/list σ αs)]
                 [_ {set (make-list (-struct-info-arity s) '•)}]))
             (define ctc-lsts : (Setof (Listof -V)) (σ@/list σ γs))

             ;; If struct has 1+ mutable fields, wrap the contract before returning
             (define κ₁
               (cond [(set-empty? mutables) κ]
                     [else
                      (define φ-wrap
                        (-φ.struct/wrap
                         s
                         (for/list : (Listof (Option -α)) ([γ γs] [i (in-naturals)])
                           (and (∋ mutables i) γ))
                         l³
                         pos))
                      (-kont φ-wrap κ)]))
             
             ;; Yield a monitoring state for each contract-list×field-list combination
             (for*/set: : (Setof -Δς) ([ctc-lst ctc-lsts] [fld-lst fld-lsts])
               (define field-mons : (Listof -Mon)
                 (for/list ([Ci ctc-lst] [Vi fld-lst] [e_ctc e_ctcs] [e_fld e_flds])
                   (-Mon (-W Ci e_ctc) (-W Vi e_fld) l³ pos)))
               (match field-mons
                 ['() (-Δς (-W (list (-St s '())) (-?@ k)) Γ-ok κ₁ '() '() '())]
                 [(cons mon mons*)
                  (define φ-mon (-φ.@ mons* (list (-W k k)) (-src-loc lo pos)))
                  (define κ₂ (-kont φ-mon κ₁))
                  (-Δς mon Γ-ok κ₂ '() '() '())])))))
    (cond
      [(and ς-ok ς-bad) (set-add ς-ok ς-bad)]
      [ς-ok ς-ok]
      [else (assert ς-bad)]))

  (match (MσΓ⊢V∈C M σ Γ W_v W_c)
    ['✓
     (define Γ* (Γ+ Γ (-?@ e_c e_v)))
     (-Δς (-W (list V) e_v) Γ* κ '() '() '())]
    ['X
     (define Γ* (Γ+ Γ (-not (-?@ e_c e_v))))
     (-Δς (-blm l+ lo C (list V)) Γ* κ '() '() '())]
    ['?
     (match C
       [(-=>i xs cs Cs d ρ_d Γ_d) (↦=>i xs cs Cs d ρ_d Γ_d)]
       [(-St/C s γs) (↦struct/c s γs)]
       [(-μ/C x c) (error '↦mon "μ/c")]
       [(-X/C x) (error '↦mon "ref")]
       [(-St (≡ -s-and/c) (list γ₁ γ₂)) (↦and/c γ₁ γ₂)]
       [(-St (≡ -s-or/c ) (list γ₁ γ₂)) (↦or/c γ₁ γ₂)]
       [(-St (≡ -s-not/c) (list α)) (↦not/c α)]
       [_
        (define κ* (-kont (-φ.if (-W (list V) e_v) (-blm l+ lo C (list V))) κ))
        (-Δς (-W (list V) e_v) Γ
             (-kont (-φ.@ '() (list W_c) (-src-loc lo pos)) κ*) '() '() '())])]))

(: ↦FC : -WV -WV -Γ -κ -σ -Ξ -M Mon-Party Integer → -Δς*)
;; Stepping rules for monitoring flat contracts
(define (↦FC W_c W_v Γ κ σ Ξ M l pos)
  (match-define (-W C e_c) W_c)
  (match-define (-W V e_v) W_v)
  (match C
    [(-St (-struct-info (and t (or 'and/c 'or/c)) _ _) (list γ₁ γ₂))
     (define Cs₁ (σ@ σ γ₁))
     (define Cs₂ (σ@ σ γ₂))
     (match-define (list c₁ c₂) (-struct-split e_c -s-and/c))
     (match/nd: (-V → -Δς) Cs₁
       [C₁
        (match/nd: (-V → -Δς) Cs₂
          [C₂
           (define φ
             (match t
               ['and/c (-φ.if (-FC W_v (-W C₂ c₂) l pos) (-W (list -ff) -ff))]
               ['or/c  (-φ.if (-W (list -tt) -tt) (-FC W_v (-W C₂ c₂) l pos))]))
           (-Δς (-FC (-W C₁ c₁) W_v l pos) Γ (-kont φ κ) '() '() '())])])]
    [(-St 'not/c (list γ))
     (match/nd: (-V → -Δς) (σ@ σ γ)
       [C*
        (define κ* (-kont (-φ.@ '() (list (-W 'not 'not)) -Λ) κ))
        (match-define (list e_c*) (-struct-split e_c -s-not/c))
        (-Δς (-FC (-W C* e_c*) W_v l) Γ κ* '() '() '())])]
    ;; FIXME recursive contract
    [_ (-Δς (-W (list V) e_v) Γ
            (-kont (-φ.@ '() (list W_c) (-src-loc l pos)) κ) '() '() '())]))
