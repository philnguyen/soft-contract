#lang typed/racket/base
(require racket/set racket/list racket/match racket/bool racket/function
         "../utils.rkt" "../lang.rkt" "../runtime.rkt" "../show.rkt" "../provability.rkt"
         "delta.rkt" "../machine.rkt")
(require/typed ; TODO for debugging only
 "../parse.rkt"
 [files->prog ((Listof Path-String) → .prog)])
(provide (all-defined-out)) ; TODO

(define-type .K (List .F .σ .κ* .κ*))
(define-type .res (List .σ .V))

(: ev : .prog → .ς+)
(define (ev p)
  (match-define (.prog ms e) p)
  (define step (step-p ms))
  (define Ξ : (MMap .rt/κ .K) (make-hash))
  (define M : (MMap .rt/κ .res) (make-hash))

  (: Ξ+! : .rt/κ .K → Void)
  (define (Ξ+! ctx K)
    (mmap-join! Ξ ctx K))

  (: M+! : .rt/κ .res → Void)
  (define (M+! ctx res)
    ;;(log-debug "abt to add:~nres:~n~a~nctx:~n~a~n~n" res ctx)
    (match-define (list σ V) res)
    (define res* (hash-ref M ctx (λ () ∅)))
    (define del
      (for/fold ([del : (Setof .res) ∅]) ([r : .res res*])
        (match-define (list σ0 V0) r)
        (cond
          ;; FIXME temp
          [((⊑ σ σ0) V V0) (set-add del (list σ V))]
          [((⊑ σ0 σ) V0 V) (set-add del (list σ0 V0))]
          [else del])))
    (hash-set! M ctx (set-subtract (set-add res* (list σ V)) del)))

  (: upd-M! : .rt/κ .res .res → Void)
  (define (upd-M! ctx res0 resi)
    (hash-update! M ctx (λ ([s : (Setof .res)])
                          (set-add (set-remove s res0) resi))))

  (: Ξ@ : .rt/κ → (Listof .K)) ; FIXME force randomness to test
  (define (Ξ@ ctx) (shuffle (set->list (hash-ref Ξ ctx (λ () ∅)))))

  (: M@ : .rt/κ → (Listof .res)) ; FIXME force randomness to test
  (define (M@ ctx) (shuffle (set->list (hash-ref M ctx (λ () ∅)))))

  (: m-opaque? : Module-Path → Boolean)
  (define (m-opaque? path)
    ;; FIXME implement
    (or (equal? path ☠) (equal? path '†)))

  (: step* : .ς → .ς+)
  (define (step* ς)
    (define-set ans : .ς)
    (define-set seen : .ς)

    (: resume : .res .K .rt/κ → Void)
    ; ans: the answer to plug in
    ; ctx: pending context
    ; rt: which context to return to
    (define (resume ans ctx rt)
      (match-let* ([(list σ0 V0) ans]
                   [(list F σk l r) ctx])
        ; avoid bogus branches
        (when (for/and : Any ([i (in-hash-keys F)])
                (let ([j (hash-ref F i)])
                  (and (or ((⊑ σ0 σk) (σ@ σ0 i) (σ@ σk j))
                           ((⊑ σk σ0) (σ@ σk j) (σ@ σ0 i)))
                       #t))) ; just to force boolean
          (match-let* ([k (append l (list* (.blr/κ F σ0 V0) rt r))]
                       [(cons σk′ F′)
                        (for/fold ([acc : (Pairof .σ .F) (cons σk F)]) ([i (in-hash-keys F)])
                          (match-define (cons σ F) acc)
                          (match-define (list σ′ _ F′) (transfer σ0 (.L i) σ F))
                          (cons σ′ F′))]
                       [(list σk′′ V-new _) (transfer σ0 V0 σk′ F′)]
                       [ς (.ς (-Vs V-new) σk′′ k)])
            (let ([ς^ (canon ς)])
              ;;(log-debug "canon:~n~a~n~n" ς^)
              (unless (seen-has? ς^)
                #;(log-debug "UNSEEN!~n~n")
                (seen-add! ς^)
                (visit ς)))))))

    ;; imperative DFS speeds interpreter up by ~40%
    ;; from not maintaining an explicit frontier set
    (: visit : .ς → Void)
    (define (visit ς)
      (match ς
        ;; record final states, omit blames on top, havoc, and opaque modules
        [(? final? ς)
         ;;(log-debug "------~n~n")
         (unless (match? ς (.ς (.blm (or #f (? (λ (x) (equal? x ☠))) (? m-opaque?)) _ _ _) _ _))
           (ans-add! ς))]
        ;; remember waiting context and plug any available answers into it
        [(.ς (cons ctx F) σ k)
         (match-define (cons l r) (split-κ* ctx k))
         (define K (list F σ l r))
         (Ξ+! ctx K)
         (for ([res : .res (M@ ctx)])
           (resume res K ctx))]
        ;; remember returned value and return to any other waiting contexts
        [(.ς (? .V? V) σ (cons (? .rt/κ? ctx) k))
         (define res (list σ V))
         (M+! ctx res)
         (for ([K : .K (Ξ@ ctx)])
           (resume res K ctx))
         (visit (.ς V σ k))]
        ;; blur value in M table ; TODO: this is a hack
        [(.ς (? .V? V) σ (cons (.blr/κ F σ0 V0) (cons (? .rt/κ? ctx) k)))
         (match-define (cons σ′ Vi) (⊕ σ0 V0 σ V))
         (define σi (⊕ σ0 σ′ F))
         (define res0 (list σ0 V0))
         (define resi (list σi Vi))
         (when ((⊑ σ0 σi) V0 Vi)
           (upd-M! ctx res0 resi))
         (for ([K : .K (Ξ@ ctx)])
           (resume resi K ctx))
         (visit (.ς V σ k))]
        ; FIXME HACK
        [(.ς (? .V? V) σ (cons (.blr/κ F1 σ1 V1) (cons (.blr/κ F0 σ0 V0) k)))
         ;;(log-debug "B: ~a  ⊕  ~a  =  ~a~n~n" (show-V σ V0) (show-V σ V1) (show-V σ (⊕ V0 V1)))
         ;;(log-debug "Blur: ~a with ~a~n~n" (show-E σ V0) (show-E σ V1))
         (match-let* ([(cons σ′ Vi) (⊕ σ0 V0 σ1 V1)]
                      [σi (⊕ σ0 σ′ F0)])
           (visit (.ς V σ (cons (.blr/κ F1 σi Vi) k))))]
        ;; FIXME hack
        [(.ς (? .V?) _ (cons (? .recchk/κ?) _))
         (let ([ς^ ς])
           (unless (seen-has? ς^)
             (seen-add! ς^)
             (match (step ς)
               [(? set? s) (for ([ςi s]) (visit ςi))]
               [(? .ς? ςi) (visit ςi)])))]
        ;; do regular 1-step on unseen state
        [_ (match (dbg/off 'step (step ς))
             [(? set? s) (for ([ςi s]) (visit ςi))]
             [(? .ς? ςi) (visit ςi)])]))
    ;; "main"
    (begin
      (visit ς)
      ans))

  (step* (inj e)))

(: step-p : (Listof .module) → (.ς → .ς*))
(define (step-p ms)

  (define HAVOC
    (match-let ([(? .λ? v) (.ref->expr ms (.ref havoc-id ☠))])
      (→V (.λ↓ v ρ∅))))

  ; promote havoc to meta-language level to reduce excessive splits
  ; in the presence of lots of struct declaration
  (: havoc : .V .σ .κ* → .ς+)
  (define (havoc V σ k)
    (match (step-@ HAVOC (list V) ☠ σ k)
      [(? set? s) s]
      [(? .ς? ς) (set ς)]))

  (: step-β : .λ↓ (Listof .V) Mon-Party .σ .κ* → .ς)
  (define (step-β f Vx l σ k)
    ;;(log-debug "Stepping ~a~n~n" (show-U σ f))
    (match f
      [(.λ↓ (.λ (? integer? n) e) ρ)
       (cond
         [(= (length Vx) n)
          (define seens (apps-seen k σ f Vx))
          (or
           (for/or : (U #f .ς) ([res : (Pairof .rt/κ (Option .F)) seens]
                                #:when (.F? (cdr res)))
             (match-define (cons ctx (? .F? F)) res)
             (.ς (cons ctx F) σ k))
           (for/or : (U #f .ς) ([res : (Pairof .rt/κ (Option .F)) seens]
                                #:when (false? (cdr res)))
             (match-define (cons (.rt/κ σ0 _ Vx0) _) res)
             (match-define (cons σ1 Vx1) (⊕ σ0 Vx0 σ Vx))
             (.ς (.↓ e (ρ++ ρ Vx1)) σ1 (cons (.rt/κ σ1 f Vx1) k)))
           (.ς (.↓ e (ρ++ ρ Vx)) σ (cons (.rt/κ σ f Vx) k)))]
         [else (.ς (.blm l 'Λ (Prim (length Vx)) (arity=/C n)) σ k)])]
      [(.λ↓ (.λ (cons n _) e) ρ)
       (error 'TODO "varargs")]))

  (: step-@ : .V (Listof .V) Mon-Party .σ .κ* → .ς*)
  (define (step-@ Vf V* l σ k)
    #;(log-debug "step-@:~n~a~n~a~n~n" (show-Ans σ Vf) (map (curry show-E σ) V*)) ;TODO reenable
    #;(log-debug "step-@:~nσ:~n~a~nf:~n~a~nx:~n~a~n~n" σ Vf V*)
    (match Vf
      [(.// U C*)
       (match U
         [(? .o? o) (match/nd (dbg/off '@ (δ σ o V* l)) [(cons σa A) (.ς A σa k)])]
         [(? .λ↓? f) (step-β f V* l σ k)]
         [(.Ar (.// (.Λ/C C* D v?) _) Vg (and l³ (list _ _ lo)))
          (let* ([V# (length V*)]
                 [C# (length C*)]
                 [n (if v? (- C# 1) #f)])
            (if (if v? (>= V# (- C# 1)) (= V# C#))
                (.ς (-Vs Vg) σ (cons (.indy/κ C* V* '() D n l³) k))
                (.ς (.blm l lo (Prim (length V*))(if v? (arity≥/C (- C# 1)) (arity=/C C#))) σ k)))]
         [_
          (match/nd (δ σ 'procedure? (list Vf) 'Λ)
            [(cons σt (-Vs (.// (.b #t) _))) (error "impossible" (show-V σt Vf))]
            [(cons σf (-Vs (.// (.b #f) _))) (.ς (.blm l 'Λ Vf PROC/C) σf k)])])]
      [(and L (.L i))
       (match/nd (δ σ 'procedure? (list L) 'Λ)
         [(cons σt (-Vs (.// (.b #t) _)))
          (match/nd (δ σt 'arity-includes? (list L (Prim (length V*))) 'Λ)
            [(cons σt (-Vs (.// (.b #t) _)))
             (match (σ@ σt i)
               [(and V (or (.// (? .λ↓?) _) (.// (? .Ar?) _))) (step-@ V V* l σt k)]
               [(? .μ/V? Vf)
                (let ([seens (μs-seen k σt Vf V*)])
                  (or
                   (for/or : (U #f .ς+) ([seen seens] #:when (hash? seen))
                     #;(log-debug "case 1~n") ∅)
                   (for/or : (U #f .ς*) ([seen seens] #:when (cons? seen))
                     (match-let* ([(cons σ0 Vx0) seen]
                                  [(cons σi Vxi) (⊕ σ0 Vx0 σt V*)])
                       (match/nd: (.V → .ς) (unroll Vf)
                         [Vj (match-let ([(cons σi′ Vj) (alloc σi Vj)])
                               #;(log-debug "case 2~n")
                               (step-@ Vj Vxi l σi′ (cons (.μ/κ Vf Vxi σi) k)))])))
                   (match/nd: (.V → .ς) (unroll Vf)
                     [Vj (match-let ([(cons σi Vj) (alloc σt Vj)])
                           #;(log-debug "case 3~n")
                           #;(log-debug "0: ~a~n1: ~a~n~n" (show-V σ0 Vx0) (show-V σt V*))
                           (step-@ Vj V* l σi (cons (.μ/κ Vf V* σt) k)))])))]
               [_
                (let-values ([(havocs) (for/fold ([s : (Setof .ς) ∅]) ([V V*])
                                         (set-union s (havoc V σt k)))]
                             [(σ′ La) (σ+ σt)])
                  (set-add havocs (.ς (-Vs La) σ′ k)))])]
            [(cons σf (-Vs (.// (.b #f) _))) (.ς (.blm l 'Λ Vf (arity-includes/C (length V*))) σf k)])]
         [(cons σf (-Vs (.// (.b #f) _))) (.ς (.blm l 'Λ Vf PROC/C) σf k)])]
      #;[(? .μ/V? Vf) (match/nd: (.V → .ς) (unroll Vf)
                        [Vf (step-@ Vf V* l σ k)])]))

  (: step-fc : .V .V Mon-Party .σ .κ* → .ς*)
  (define (step-fc C V l σ k)
    (match (⊢ σ V C)
      ['✓ (.ς -VsTT σ k)]
      ['X (.ς -VsFF σ k)]
      ['?
       (match C
         [(.// U D*)
          (match U
            [(and (.μ/C x C′) U)
             (cond
               [(chk-seen? k U (V-abs σ V)) (match-let ([(cons σ′ _) (refine σ V C)])
                                              (.ς -VsTT σ′ k))]
               [else (match-let ([(cons σt _) (refine σ V C)]
                                 [(cons σf _) (refine σ V (.¬/C C))])
                       {set (.ς -VsTT σt k) (.ς -VsFF σf k)})])]
            [(.St (.id 'and/c 'Λ) (list C1 C2)) (and/ς (list (.FC C1 V l) (.FC C2 V l)) σ k)]
            [(.St (.id 'or/c 'Λ) (list C1 C2)) (or/ς (list (.FC C1 V l) (.FC C2 V l)) σ k)]
            [(.St (.id 'not/c 'Λ) (list C′))
             (.ς (.FC C′ V l) σ (cons (.@/κ '() (list (Prim 'false?)) l) k))]
            [(.St/C t C*)
             (match/nd (δ σ (.st-p t (length C*)) (list V) l)
               [(cons σt (-Vs (.// (.b #t) _)))
                (match-let ([(.// (.St t V*) _) (σ@ σt V)])
                  (and/ς (for/list ([Vi V*] [Ci C*]) (.FC Ci Vi l)) σt k))]
               [(cons σf (-Vs (.// (.b #f) _))) (.ς -VsFF σf k)])]
            [_ (step-@ C (list V) l σ k)])]
         [(.L _) (step-@ C (list V) l σ k)])]))

  (: step-▹ : .V .V Mon-Info .σ .κ* → .ς*)
  (define (step-▹ C V l³ σ k)
    #;(log-debug "Mon:~nC:~a~nV:~a~nσ:~a~nk:~a~n~n" C V σ k)
    (match-let ([(list l+ l- lo) l³])
      (match (⊢ σ V C) ; want a check here to reduce redundant cases for recursive contracts
        ['✓ (.ς (-Vs V) σ k)]
        ['X (.ς (.blm l+ lo V C) σ k)]
        ['?
         (match C
           [(.L i)
            (match-define (cons σt Vt) (refine σ V C))
            (match-define (cons σf Vf) (refine σ V (.¬/C C)))
            {set (.ς (-Vs Vt) σt k) (.ς (-Vs Vf) σf k)}]
           [(.// Uc C*)
            (match Uc
              [(and (.μ/C x C′) Uc)
               (cond
                 [(chk-seen? k Uc (V-abs σ V))
                  (match-let ([(cons σ′ V′) (dbg/off 'ho (refine σ V C))])
                    (.ς (-Vs V′) σ′ k))]
                 ; hack to speed things up
                 [(flat/C? σ C)
                  #;(log-debug "Abt to refine:~nσ:~n~a~nV:~n~a~nC:~n~a~n~n" σ V C)
                  (match-let ([(cons σt Vt) (refine σ V C)]
                                            [(cons σf _) (refine σ V (.¬/C C))])
                                  {set (.ς (-Vs Vt) σt k) (.ς (.blm l+ lo V C) σf k)})]
                 [else (.ς (-Vs V) σ (list* (.▹/κ (cons (unroll/C Uc) #f) l³) (.recchk/κ Uc (V-abs σ V)) k))])]
              [(.St (.id 'and/c 'Λ) (list Dl Dr)) (.ς (-Vs V) σ (▹/κ1 Dl l³ (▹/κ1 Dr l³ k)))]
              [(.St (.id 'or/c 'Λ) (list Dl Dr))
               (.ς (.FC Dl V lo) σ (cons (.if/κ (.Assume V Dl) (.Mon (-Vs Dr) (-Vs V) l³)) k))]
              [(.St (.id 'not/c 'Λ) (list D))
               (.ς (.FC D V lo) σ (cons (.if/κ (.blm l+ lo V C) (.Assume V C)) k))]
              [(.St/C t C*)
               (let ([n (length C*)])
                 (match/nd (δ σ (.st-p t n) (list V) lo)
                   [(cons σt (-Vs (.// (.b #t) _)))
                    (match-let ([(.// (.St t V*) _) (dbg/off '▹ (σ@ σt V))])
                      (.ς (-Vs (→V (.st-mk t n))) σt
                          (cons (.@/κ (for/list ([C C*] [V V*]) (.Mon (-Vs C) (-Vs V) l³)) '() lo) k)))]
                   [(cons σf (-Vs (.// (.b #f) _))) (.ς (.blm l+ lo V (→V (.st-p t n))) σf k)]))]
              [(and Uc (.Λ/C Cx* D v?))
               (match/nd (δ σ 'procedure? (list V) lo)
                 [(cons σt (-Vs (.// (.b #t) _)))
                  (match v?
                    [#f (match/nd (δ σt 'arity-includes? (list V (Prim (length Cx*))) lo)
                          [(cons σt (-Vs (.// (.b #t) _))) (.ς (-Vs (→V (.Ar C V l³))) σt k)]
                          [(cons σf (-Vs (.// (.b #f) _)))
                           (.ς (.blm l+ lo V (arity-includes/C (length Cx*))) σf k)])]
                    [#t (match/nd (δ σt 'arity>=? (list V (Prim (- (length Cx*) 1))) lo)
                          [(cons σt (-Vs (.// (.b #t) _))) (.ς (-Vs (→V (.Ar C V l³))) σt k)]
                          [(cons σf (-Vs (.// (.b #f) _)))
                           (.ς (.blm l+ lo V (arity≥/C (- (length Cx*) 1))) σf k)])])]
                 [(cons σf (-Vs (.// (.b #f) _))) (.ς (.blm l+ lo V PROC/C) σf k)])]
              [_ (.ς (.FC C V lo) σ (cons (.if/κ (.Assume V C) (.blm l+ lo V C)) k))])])])))

  (: step-E : .E .σ .κ* → .ς*)
  (define (step-E E σ k)
    #;(log-debug "E: ~a~n~n" E)
    (match E
      [(.↓ e ρ)
       (match e
         [(? .•?) (let-values ([(σ′ L) (σ+ σ)]) (.ς (-Vs L) σ′ k))]
         [(? .v? v) (.ς (-Vs (close v ρ)) σ k)]
         [(.x sd)
          (when (.X/V? (ρ@ ρ sd)) (error "STOP!"))
          (.ς (-Vs (ρ@ ρ sd)) σ k)]
         [(? .x/c? x) (.ς (-Vs (ρ@ ρ x)) σ k)]
         [(and ref (.ref (.id name ctx) ctx)) (.ς (.↓ (.ref->expr ms ref) ρ∅) σ k)]
         [(and ref (.ref (.id name in) ctx))
          (.ς (.↓ (.ref->ctc ms ref) ρ∅) σ
              (cons (.▹/κ  (cons #f (.↓ (.ref->expr ms ref) ρ∅)) (list in ctx in)) k))]
         [(.let-values '() e _) (step-E (.↓ e ρ) σ k)]
         [(.let-values (cons (cons nₓ eₓ) bnds) e ctx)
          (.ς (.↓ eₓ ρ) σ (cons (.let-values/κ nₓ bnds '() ρ e ctx) k))]
         [(.@ f xs l) (.ς (.↓ f ρ) σ (cons (.@/κ (for/list ([x xs]) (.↓ x ρ)) '() l) k))]
         [(.@-havoc x)
          (define V
            ;; Abstract values of form (μx._) are safe to discard for havoc-ing
            (match (ρ@ ρ x)
              [(? .//? V) V]
              [(.L i) (match (σ@ σ i) ; TODO rewrite
                        [(? .//? V) V]
                        [_ #f])]
              [_ #f]))
          (match V
            [(and V (.// U C*))
             ; always alloc the result of unroll
             ; FIXME: rewrite 'unroll' to force it
             (match-let ([(cons σ V) (alloc σ V)])
               #;(log-debug "havoc: ~a~n~n" (show-V σ V))
               (match U
                 [(.λ↓ (.λ formals _) _)
                  (let-values ([(σ′ Ls)
                                (match formals
                                  [(? integer? n) (σ++ σ n)]
                                  [(cons n _) (σ++ σ (+ 1 n))])])
                    (step-@ V Ls ☠ σ′ k))]
                 [(.Ar (.// (.Λ/C Cx _ _) _) _ _)
                  (let-values ([(σ′ Ls) (σ++ σ (length Cx))])
                    (step-@ V Ls ☠ σ′ k))]
                 [_ ∅]))]
            [#f ∅])]
         #;[(.apply f xs l) (.ς (.↓ f ρ) σ (cons (.apply/ar/κ (.↓ xs ρ) l) k))]
         [(.if i t e) (.ς (.↓ i ρ) σ (cons (.if/κ (.↓ t ρ) (.↓ e ρ)) k))]
         [(.amb e*) (for/set: : (Setof .ς) ([e e*]) (.ς (.↓ e ρ) σ k))]
         [(.μ/c x e) (.ς (.↓ e (ρ+ ρ x (→V (.X/C x)))) σ (cons (.μc/κ x) k))]
         [(.->i '() d v?) (.ς (-Vs (→V (.Λ/C '() (.↓ d ρ) v?))) σ k)]
         [(.->i (cons c cs) d v?) (.ς (.↓ c ρ) σ (cons (.λc/κ cs '() d ρ v?) k))]
         [(.struct/c t '()) (.ς (-Vs (→V (.st-p t 0))) σ k)]
         [(.struct/c t (cons c c*)) (.ς (.↓ c ρ) σ (cons (.structc/κ t c* ρ '()) k))])]
      [(.Mon C E l³) (.ς C σ (cons (.▹/κ (cons #f E) l³) k))]
      [(.FC C V l) (step-fc C V l σ k)]
      [(.Assume V C) (match-let ([(cons σ′ V′) (refine σ V C)]) (.ς (-Vs V′) σ′ k))]))

  (: step-V : .V .σ .κ .κ* → .ς*)
  (define (step-V V σ κ k)
    (when (match? V (.// '• _))
      (error 'Impossible "~a" (show-ς (.ς (-Vs V) σ (cons κ k)))))
    (match κ
      [(.if/κ E1 E2) (match/nd (δ σ 'false? (list V) 'Λ)
                       [(cons σt (-Vs (.// (.b #f) _))) (.ς E1 σt k)]
                       [(cons σf (-Vs (.// (.b #t) _))) (.ς E2 σf k)])]


      
      [(.@/κ (cons E1 Er) V* l) (.ς E1 σ (cons (.@/κ Er (cons V V*) l) k))]
      [(.@/κ '() V* l)
       (match-define (cons Vf Vx*) (reverse (cons V V*)))
       (step-@ Vf Vx* l σ k)]

      #;[(.apply/ar/κ E l) (.ς E σ (cons (.apply/fn/κ V l) k))]
      #;[(.apply/fn/κ Vf l) (step-apply Vf V l σ k)]

      [(.▹/κ (cons #f (? .E? E)) l³) (.ς E σ (cons (.▹/κ (cons V #f) l³) k))]
      [(.▹/κ (cons (? .V? C) #f) l³) (step-▹ C V l³ σ k)]

      [(.rt/κ _ _ _) (.ς (-Vs V) σ k)]
      [(.recchk/κ _ _) (.ς (-Vs V) σ k)]
      [(.μ/κ _ _ _) (.ς (-Vs V) σ k)]

      ;; indy
      [(.indy/κ (list Ci) (cons Vi Vr) Vs↓ D n l³) ; repeat last contract, handling var-args
       (step-▹ Ci Vi (swap-parties l³) σ (cons (.indy/κ (list Ci) Vr (cons V Vs↓) D n l³) k))]
      [(.indy/κ (cons Ci Cr) (cons Vi Vr) Vs↓ D n l³)
       (step-▹ Ci Vi (swap-parties l³) σ (cons (.indy/κ Cr Vr (cons V Vs↓) D n l³) k))]
      [(.indy/κ _ '() Vs↓ (.↓ d ρ) n l³) ; evaluate range contract
       (match-let ([(and V* (cons Vf Vx*)) (reverse (cons V Vs↓))])
         (.ς (.↓ d (ρ++ ρ Vx* n)) σ (cons (.indy/κ '() '() V* #f n l³) k)))]
      [(.indy/κ _ '() (cons Vf Vx) #f _ (and l³ (list l+ _ _))) ; apply inner function
       #;(log-debug "range: ~a~n~n" (show-E σ V))
       (step-@ Vf Vx l+ σ (▹/κ1 V l³ k))]

      ; contracts
      [(.μc/κ x) (.ς (-Vs (→V (.μ/C x V))) σ k)]
      [(.λc/κ '() c↓ d ρ v?)
       (.ς (-Vs (→V (.Λ/C (reverse (cons V c↓)) (.↓ d ρ) v?))) σ k)]
      [(.λc/κ (cons c cs) c↓ d ρ v?) (.ς (.↓ c ρ) σ (cons (.λc/κ cs (cons V c↓) d ρ v?) k))]
      [(.structc/κ t '() _ c↓) (.ς (-Vs (→V (.St/C t (reverse (cons V c↓))))) σ k)]
      [(.structc/κ t (cons c c*) ρ c↓) (.ς (.↓ c ρ) σ (cons (.structc/κ t c* ρ (cons V c↓)) k))]))

  (: step-Vs : (Listof .V) .σ .κ .κ* → .ς*)
  (define (step-Vs Vs σ κ k)
    (match κ
      [(.let-values/κ n bnds vals ρ e ctx)
       (cond
         [(= n (length Vs))
          (match bnds
            [(list) (.ς (.↓ e (ρ++ (ρ++ ρ vals) Vs)) σ k)]
            [(cons (cons nₓ eₓ) bnds*)
             (.ς (.↓ eₓ ρ) σ
                 (cons (.let-values/κ nₓ bnds* (append vals Vs #|order matters|#) ρ e ctx) k))])]
         [else (.ς (.blm ctx 'let-values (Prim (length Vs)) (=/C (Prim n))) σ k)])]
      [κ (match Vs
           [(list V) (step-V V σ κ k)]
           [_ (todo "Blame sub-expression for wrong arity")])]))

  (match-lambda
    [(.ς (.Vs Vs) σ (cons κ k)) (step-Vs Vs σ κ k)]
    [(.ς (? .E? E) σ k) (step-E E σ k)]))

(: apps-seen : .κ* .σ .λ↓ (Listof .V) → (Listof (Pairof .rt/κ (Option .F))))
(define (apps-seen k σ f Vx)
  #;(log-debug "apps-seen~nf: ~a~nk: ~a~n~n" (show-V σ∅ (→V f)) (show-k σ∅ k))
  (for/fold ([acc : (Listof (Pairof .rt/κ (Option .F))) '()]) ([κ k])
    (match κ
      [(and κ (.rt/κ σ0 f0 Vx0))
       (if (equal? f0 f)
           (cons (ann (cons κ ((⊑ σ σ0) Vx Vx0))
                      (Pairof .rt/κ (Option .F)))
                 acc)
           acc)]
      [_ acc])))

(: μs-seen : .κ* .σ .μ/V (Listof .V) → (Listof (U .F (Pairof .σ (Listof .V)))))
(define (μs-seen k σ f Vx)
  #;(log-debug "apps-seen~nf: ~a~nk: ~a~n~n" (show-V σ∅ (→V f)) (show-k σ∅ k))
  (for/fold ([acc : (Listof (U .F (Pairof .σ (Listof .V)))) '()]) ([κ k])
    (match κ
      [(.μ/κ g Vx0 σ0) (match ((⊑ σ σ0) Vx Vx0)
                         [#f (cons (ann (cons σ0 Vx0) (Pairof .σ (Listof .V))) acc)]
                         [(? hash? F) (cons F acc)])]
      [_ acc])))

(: split-κ* : .rt/κ .κ* → (Pairof .κ* .κ*))
(define (split-κ* κ k)
  #;(log-debug "Split:~n~a~n~n~a~n~n" κ k)
  (let: go ([l : .κ* '()] [k k])
    (match k
      ['() (error "WTF")]
      [(cons (? .rt/κ? κ′) kr)
       (if (equal? κ κ′) (cons (reverse l) kr) (go (cons κ′ l) kr))]
      [(cons κ kr) (go (cons κ l) kr)])))

(: chk-seen? : .κ* .μ/C .V → Boolean)
(define (chk-seen? k C V)
  (for/or ([κ k] #:when (match? κ (? .recchk/κ?)))
    (match-let ([(.recchk/κ C′ V′) κ])
      (and (equal? C′ C) (equal? V′ V)))))

;; for debugging
(define (e [p : Path-String])
  (set->list (ev (files->prog (list p)))))


;; rename all labels to some canonnical form based on the expression's shape
;; relax, this only happens a few times, not that expensive
(: canon : .ς → .ς)
(define (canon ς)
  (match-define (.ς (? .E? E) σ k) ς)
  (define F F∅)
  (: alloc! : Integer → Integer)
  (define (alloc! i)
    (match (hash-ref F i #f)
      [(? integer? j) j]
      [#f (let ([j (hash-count F)])
            (set! F (hash-set F i j))
            j)]))

  (: go! : (case→ [.V → .V] [.↓ → .↓] [.E → .E]
                  [.μ/C → .μ/C] [.λ↓ → .λ↓] [.U → .U] [.ρ → .ρ] [.κ → .κ] [.κ* → .κ*]
                  [(Listof .V) → (Listof .V)] [(Listof .E) → (Listof .E)]
                  [.σ → .σ]))
  (define (go! x)
    (match x
      ; E
      [(.↓ e ρ) (.↓ e (go! ρ))]
      [(.FC C V ctx) (.FC (go! C) (go! V) ctx)]
      [(.Mon C E l) (.Mon (go! C) (go! E) l)]
      [(.Assume V C) (.Assume (go! V) (go! C))]
      [(.blm f g V C) (.blm f g (go! V) (go! C))]
      ; V
      [(.L i) (.L (alloc! i))]
      [(.// U C*) (.// (go! U) C*)]
      [(? .μ/V? V) V]
      [(? .X/V? V) V]
      ; U
      [(.Ar C V l) (.Ar (go! C) (go! V) l)]
      [(.St t V*) (.St t (go! V*))]
      [(.λ↓ f ρ) (.λ↓ f (go! ρ))]
      [(.Λ/C C* D v?) (.Λ/C (go! C*) (go! D) v?)]
      [(.St/C t V*) (.St/C t (go! V*))]
      [(.μ/C x V) (.μ/C x (go! V))]
      [(? .X/C? x) x]
      [(? .prim? p) p]
      ; ρ
      [(.ρ m l) (.ρ (for/hash : (Map (U Integer Symbol) .V) ([(i V) (in-hash m)])
                      (values i (go! V)))
                    l)]
      ; κ
      [(.if/κ t e) (.if/κ (go! t) (go! e))]
      [(.@/κ e* v* l) (.@/κ (go! e*) (go! v*) l)]
      [(.▹/κ (cons C E) l)
       (.▹/κ (cond [(and (false? C) (.E? E)) (cons #f (go! E))]
                   [(and (.V? C) (false? E)) (cons (go! C) #f)]
                   [else (error "impossible!")])
             l)]
      [(.indy/κ c x x↓ d v? l)
       (.indy/κ (go! c) (go! x) (go! x↓) (if (.↓? d) (go! d) #f) v? l)]
      [(? .μc/κ? x) x]
      [(.λc/κ c c↓ d ρ v?) (.λc/κ c (go! c↓) d (go! ρ) v?)]
      [(.structc/κ t c ρ c↓) (.structc/κ t c (go! ρ) (go! c↓))]
      #;[(.rt/κ σ f x) (.rt/κ σ (go! f) (go! x))]
      #;[(.blr/κ G σ V) (.blr/κ (for/fold: ([G′ : .F G]) ([i (in-hash-keys G)])
                                (let ([j (alloc! i)]
                                      [k (alloc! (hash-ref G i))])
                                  (hash-set G′ j k)))
                              σ (go! V))]
      #;[(.recchk/κ C V) (.recchk/κ (go! C) (go! V))]
      [(.μ/κ f xs σ) (.μ/κ f (go! xs) σ)]
      ; list
      [(? list? l)
       (for/list ([i l] #:unless (match? i (? .rt/κ?) (? .blr/κ?) (? .recchk/κ?))) (go! i))]))

  (: fixup/V : .V → .V)
  (define fixup/V
    (match-lambda
     [(? .L? x) x]
     [(.// U Cs) (.// (fixup/U U) (subst/L Cs F))]
     [(.μ/V x V*) (.μ/V x (subst/L V* F))]
     [(? .X/V? x) x]))

  (: fixup/E : (case-> (.↓ → .↓) (.E → .E)))
  (define fixup/E
    (match-lambda
     [(.↓ e ρ) (.↓ e (fixup/ρ ρ))]
     [(.FC c v l) (.FC (fixup/V c) (fixup/V v) l)]
     [(.Mon c e l) (.Mon (fixup/E c) (fixup/E e) l)]
     [(.Assume v c) (.Assume (fixup/V v) (fixup/V c))]
     [(.blm f g v c)(.blm f g (fixup/V v) (fixup/V c))]
     [(? .V? V) (fixup/V V)]))

  (: fixup/U : (case-> [.μ/C → .μ/C] [.λ↓ → .λ↓] [.U → .U]))
  (define fixup/U
    (match-lambda
     [(.Ar c v l) (.Ar (fixup/V c) (fixup/V v) l)]
     [(.St t V*) (.St t (fixup/V* V*))]
     [(.λ↓ f ρ) (.λ↓ f (fixup/ρ ρ))]
     [(.Λ/C c d v?) (.Λ/C (fixup/V* c) (fixup/E d) v?)]
     [(.St/C t V*) (.St/C t (fixup/V* V*))]
     [(.μ/C x c) (.μ/C x (fixup/V c))]
     [(? .X/C? x) x]
     [(? .prim? p) p]))

  (: fixup/ρ : .ρ → .ρ)
  (define (fixup/ρ ρ)
    (match-define (.ρ m l) ρ)
    (.ρ (for/hash : (Map (U Integer Symbol) .V) ([(i V) (in-hash m)])
          (values i (fixup/V V)))
        l))

  (: fixup/κ : .κ → .κ)
  (define fixup/κ
    (match-lambda
     [(.if/κ t e) (.if/κ (fixup/E t) (fixup/E e))]
     [(.@/κ e* v* l) (.@/κ (fixup/E* e*) (fixup/V* v*) l)]
     [(.▹/κ (cons C E) l)
      (.▹/κ (cond [(and (false? C) (.E? E)) (cons #f (fixup/E E))]
                  [(and (.V? C) (false? E)) (cons (fixup/V C) #f)]
                  [else (error 'fixup/κ "impossible")])
            l)]
     [(.indy/κ c x x↓ d v? l)
      (.indy/κ (fixup/V* c) (fixup/V* x) (fixup/V* x↓) (if (.↓? d) (fixup/E d) #f) v? l)]
     [(? .μc/κ? x) x]
     [(.λc/κ c c↓ d ρ v?) (.λc/κ c (fixup/V* c↓) d (fixup/ρ ρ) v?)]
     [(.structc/κ t c ρ c↓) (.structc/κ t c (fixup/ρ ρ) (fixup/V* c↓))]
     #;[(.rt/κ σ f x) (.rt/κ (fixup σ) (fixup f) (fixup x))]
     #;[(.blr/κ G σ V) (.blr/κ G (fixup σ) (fixup V))]
     #;[(.recchk/κ C V) (.recchk/κ (fixup C) (fixup V))]
     [(.μ/κ f xs σ) (.μ/κ f (fixup/V* xs) (fixup/σ σ))]))

  (: fixup/κ* : .κ* → .κ*)
  (define (fixup/κ* κ*) (map fixup/κ κ*))

  (: fixup/σ : .σ → .σ)
  (define (fixup/σ σ)
    (match-define (.σ m _) σ)
    (define-values (σ′ _) (σ++ σ∅ (hash-count F)))
    (for/fold ([σ′ : .σ σ′]) ([i (in-hash-keys F)])
      (match (hash-ref m i #f)
        [(? .V? Vi) (σ-set σ′ (hash-ref F i) (subst/L Vi F))]
        [#f σ′])))

  (: fixup/E* : (Listof .E) → (Listof .E))
  (define (fixup/E* l) (map fixup/E l))

  (: fixup/V* : (Listof .V) → (Listof .V))
  (define (fixup/V* l) (map fixup/V l))

  (define E′ (go! E))
  (define k′ (go! k))
  (.ς (fixup/E E′) (fixup/σ σ) (fixup/κ* k′)))

