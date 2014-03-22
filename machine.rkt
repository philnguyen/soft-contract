#lang typed/racket
(require "utils.rkt" "lang.rkt" "closure.rkt" "delta.rkt" "provability.rkt" "show.rkt")
(require/typed ; TODO for debugging only
 "read.rkt"
 [read-p (Any → .p)])
(provide (all-defined-out)) ; TODO

(define-data (.κ)
  (.if/κ [t : .E] [e : .E])
  (.@/κ [e* : (Listof .E)] [v* : (Listof .V)] [ctx : Sym])
  (.▹/κ [ce : (U (Pairof #f .E) (Pairof .V #f))] [l^3 : Sym^3])
  (.indy/κ [c : (Listof .V)] [x : (Listof .V)] [x↓ : (Listof .V)]
           [d : (U #f .↓)] [v? : (U #f Int)] [l^3 : Sym^3])
  ; contract stuff
  (.μc/κ [x : Sym])
  (.λc/κ [c : (Listof .e)] [c↓ : (Listof .V)] [d : .e] [ρ : .ρ] [v? : Bool])
  (.structc/κ [t : Sym] [c : (Listof .e)] [ρ : .ρ] [c↓ : (Listof .V)])
  ; magics for termination
  (.rt/κ [σ : .σ] [f : .λ↓] [x : (Listof .V)])
  (.blr/κ [F : .F] [σ : .σ] [v : .V])
  (.recchk/κ [c : .μ/C] [v : .V]) ; where all labels are fully resolved
  ; experiment
  (.μ/κ [F : .μ/V] [xs : (Listof .V)] [σ : .σ]))
(define-type .κ* (Listof .κ))

; ctx in e's position for pending states
(struct: .ς ([e : (U (Pairof .rt/κ .F) .E)] [s : .σ] [k : .κ*]) #:transparent)
(define-type .ς+ (Setof .ς))
(define-type .ς* (U .ς .ς+))

(: final? : .ς → Bool)
(define final?
  (match-lambda [(.ς (? .blm?) _ _) #t]
                [(.ς (.V) _ (list)) #t]
                [_ #f]))

(: inj : .e → .ς)
(define (inj e)
  (.ς (.↓ e ρ∅) σ∅ empty))

(define-type .K (List .F .σ .κ* .κ*))
(define-type .res (List .σ .V))

(: ev : .p → .ς+)
(define (ev p)
  (match-define (.p (and m* (.m* _ ms)) e) p)
  (define step (step-p m*))
  (define: Ξ : (MMap .rt/κ .K) (make-hash))
  (define: M : (MMap .rt/κ .res) (make-hash))
  
  (: Ξ+! : .rt/κ .K → Void)
  (define (Ξ+! ctx K)
    #;(printf "Ξ[~a] += ~a~n~n"
              (show-κ σ ctx)
              `((σ: ,@(show-σ σ))
                (l: ,@(show-k σ l))
                (r: ,@(show-k σ r))))
    (mmap-join! Ξ ctx K))
  
  (: M+! : .rt/κ .res → Void)
  (define (M+! ctx res)
    #;(printf "abt to add:~nres:~n~a~nctx:~n~a~n~n" res ctx)    
    (match-let* ([(list σ V) res]
                 [res* (hash-ref M ctx (λ () ∅))]
                 [del                  
                  (for/fold: ([del : (Setof .res) ∅]) ([r : .res res*])
                        (match-let ([(list σ0 V0) r])
                          #;(printf "Comparing:~nV0:~n~a~nσ0:~n~a~nV1:~n~a~nσ1:~n~a~n~n"
                                  V0 σ0 V σ)
                          #;(printf "Result: ~a ~a~n~n" ((⊑ σ σ0) V V0) ((⊑ σ0 σ) V0 V))
                          (cond
                            #;[(equal? Vi V^) del]
                            ; FIXME temp
                            [((⊑ σ σ0) V V0) #;(printf "case 1~n") (set-add del (list σ V))]
                            [((⊑ σ0 σ) V0 V) #;(printf "case 2~n") (set-add del (list σ0 V0))]
                            [else #;(printf "case 3~n~n~n")del])))])
      #;(printf "old-res for:~n~a~n~n~a~n~n" (set-count res*))
      #;(printf ",")
      (hash-set! M ctx (set-subtract (set-add res* (list σ V)) del))))
  
  (: upd-M! : .rt/κ .res .res → Void)
  (define (upd-M! ctx res0 resi)
    (hash-update! M ctx (λ: ([s : (Setof .res)])
                          (set-add (set-remove s res0) resi))))
  
  (: Ξ@ : .rt/κ → (Listof .K)) ; FIXME force randomness to test
  (define (Ξ@ ctx) (shuffle (set->list (hash-ref Ξ ctx (λ () ∅)))))
  
  (: M@ : .rt/κ → (Listof .res)) ; FIXME force randomness to test
  (define (M@ ctx) (shuffle (set->list (hash-ref M ctx (λ () ∅)))))
  
  (: m-opaque? : Sym → Bool)
  (define (m-opaque? x) ; TODO: expensive?
    (match-let ([(.m _ defs) (hash-ref ms x)])
      (for/or ([d (in-hash-values defs)] #:when (match? d (cons (.•) _))) #t)))
  
  (: step* : .ς → .ς+)
  (define (step* ς)
    (define: ans : .ς+ ∅)
    (define-set: seen : .ς [seen? seen!])
    
    (: resume : .res .K .rt/κ → Void)
    ; ans: the answer to plug in
    ; ctx: pending context
    ; rt: which context to return to
    (define (resume ans ctx rt)
      (match-let* ([(list σ0 V0) ans]
                   [(list F σk l r) ctx])
        ; avoid bogus branches
        (when (for/and: : Any ([i (in-hash-keys F)])
                (let ([j (hash-ref F i)])
                  (and (or ((⊑ σ0 σk) (σ@ σ0 i) (σ@ σk j))
                           ((⊑ σk σ0) (σ@ σk j) (σ@ σ0 i)))
                       #t))) ; just to force boolean
          (match-let* ([k (append l (list* (.blr/κ F σ0 V0) rt r))]
                       [(cons σk′ F′)
                        (for/fold: ([acc : (Pairof .σ .F) (cons σk F)]) ([i (in-hash-keys F)])
                          (match-let* ([(cons σ F) acc]
                                       [(list σ′ _ F′) (transfer σ0 (.L i) σ F)])
                            (cons σ′ F′)))]
                       [(list σk′′ V-new _) (transfer σ0 V0 σk′ F′)]
                       [ς (.ς V-new σk′′ k)])
            #;(printf "Resume called with:~n res:~n~a~n K:~n~a~n rt:~n~a~nAbout to resume with:~n~a~n~n"
                    ans ctx rt ς)
            (let ([ς^ (canon ς)])
              #;(printf "canon:~n~a~n~n" ς^)
              (unless (seen? ς^)
                #;(printf "UNSEEN!~n~n")
                (seen! ς^)
                (visit ς)))
            #;(when-unseen! ς (visit ς))))))
    
    ; imperative DFS speeds interpreter up by ~40%
    ; from not maintaining an explicit frontier set
    (: visit : .ς → Void)
    (define (visit ς)
      #;(printf ".")
      #;(printf "~a~n~n" (show-ς ς))
      #;(when (match? (.ς-k ς) (cons (? .blr/κ?) (cons (not (or (? .blr/κ?) (? .rt/κ?))) _))) (error "STOP"))
      #;(match ς
        [(.ς (? .V? V) _ _) (check V)]
        [_ (void)])
      (match ς
        ; record final states, omit blames on top, havoc, and opaque modules
        [(? final? ς)
         #;(printf "------~n~n")
         (unless (match? ς (.ς [.blm (or '† '☠ (? m-opaque?)) _ _ _] _ _))
           (set! ans (set-add ans ς)))]
        ; remember waiting context and plug any available answers into it
        [(.ς (cons ctx F) σ k)
         (match-let* ([(cons l r) (split-κ* ctx k)]
                      [K (list F σ l r)])
           (Ξ+! ctx K)
           (for ([res : .res (M@ ctx)])
             (resume res K ctx)))]
        ; remember returned value and return to any other waiting contexts
        [(.ς (? .V? V) σ (cons (? .rt/κ? ctx) k))
         (let ([res (list σ V)])
           (M+! ctx res)
           (for ([K : .K (Ξ@ ctx)])
             (resume res K ctx)))
         (visit (.ς V σ k))]
        ; blur value in M table ; TODO: this is a hack
        [(.ς (? .V? V) σ (cons (.blr/κ F σ0 V0) (cons (? .rt/κ? ctx) k)))
         (match-let* ([(cons σ′ Vi) (⊕ σ0 V0 σ V)]
                      [σi (⊕ σ0 σ′ F)]
                      [res0 (list σ0 V0)]
                      [resi (list σi Vi)])
           (when ((⊑ σ0 σi) V0 Vi)
             (upd-M! ctx res0 resi))
           (for ([K : .K (Ξ@ ctx)])
             (resume resi K ctx)))
         (visit (.ς V σ k))]
        ; FIXME HACK
        [(.ς (? .V? V) σ (cons (.blr/κ F1 σ1 V1) (cons (.blr/κ F0 σ0 V0) k)))
         #;(printf "B: ~a  ⊕  ~a  =  ~a~n~n" (show-V σ V0) (show-V σ V1) (show-V σ (⊕ V0 V1)))
         #;(printf "Blur: ~a with ~a~n~n" (show-E σ V0) (show-E σ V1))
         (match-let* ([(cons σ′ Vi) (⊕ σ0 V0 σ1 V1)]
                      [σi (⊕ σ0 σ′ F0)])
           (visit (.ς V σ (cons (.blr/κ F1 σi Vi) k))))]
        ; FIXME hack
        [(.ς (? .V?) _ (cons (? .recchk/κ?) _))
         (let ([ς^ ς])
           (unless (seen? ς^)
             (seen! ς^)
             (match (step ς)
               [(? set? s) (for ([ςi s]) (visit ςi))]
               [(? .ς? ςi) (visit ςi)])))]
        ; do regular 1-step on unseen state
        [_ (match (dbg/off 'step (step ς))
             [(? set? s) #;(printf "SPLIT ~a~n~n" (set-count s)) ; FIXME force randomness to test
                         (for ([ςi (shuffle (set->list s))]) #;(printf "BRANCH:~n~n") (visit ςi) #;(when-unseen! ςi (visit ςi)))]
             [(? .ς? ςi) (visit ςi) #;(when-unseen! ςi (visit ςi))])]))
    
    ;; "main"
    (begin
      (visit ς)
      #;(printf "#states: ~a, ~a base cases, ~a contexts~n~n"
                (set-count seen)
                (list (hash-count M) (for/sum: : Int ([s (in-hash-values M)]) (set-count s)))
                (list (hash-count Ξ) (for/sum: : Int ([s (in-hash-values Ξ)]) (set-count s))))
      #;(printf "contexts:~n~a~n~n" (hash->list Ξ))
      ans))
  
  (step* (inj e)))

(define-syntax-rule (match/nd v [p e ...] ...) (match/nd: (.Ans → .ς) v [p e ...] ...))
(: step-p : .m* → (.ς → .ς*))
(define (step-p m*)  
  (match-define (.m* _ ms) m*)
  
  (: ref-e : Sym Sym → .e)
  (define (ref-e m x)
    (match-let ([(.m _ defs) (hash-ref ms m)])
      (car (hash-ref defs x))))
  
  (: ref-c : Sym Sym → .e)
  (define (ref-c m x)
    (match-let ([(.m _ decs) (hash-ref ms m)])
      (match (cdr (hash-ref decs x))
        [(? .e? c) c]
        [_ (error (format "module ~a does not export ~a" m x))])))
  
  (define HAVOC (match-let ([(? .λ? v) (ref-e '☠ 'havoc)]) (→V (.λ↓ v ρ∅))))
  
  ; promote havoc to meta-language level to reduce excessive splits
  ; in the presence of lots of struct declaration
  (: havoc : .V .σ .κ* → .ς+)
  (define (havoc V σ k)
    (match (step-@ HAVOC (list V) '☠ σ k)
      [(? set? s) s]
      [(? .ς? ς) (set ς)]))
  
  (: step-β : .λ↓ (Listof .V) Sym .σ .κ* → .ς)
  (define (step-β f Vx l σ k)
    #;(printf "Stepping ~a~n~n" (show-U σ f))
    (match-let* ([(.λ↓ (.λ n e v?) ρ) f])
      (match v?
        [#f (if (= (length Vx) n)
                (let ([seens (apps-seen k σ f Vx)])                  
                  #;(printf "Chain:~n~a~n~n" seens)
                  (or
                   (for/or: : (U #f .ς) ([res : (Pairof .rt/κ (Option .F)) seens]
                                         #:when (.F? (cdr res)))
                     (match-let ([(cons ctx (? .F? F)) res])
                       #;(printf "Seen, repeated:~nold:~n~a~nNew:~n~a~nF: ~a~n~n"
                               ctx (show-V σ Vx) F)
                       (.ς (cons ctx F) σ k)))
                   (for/or: : (U #f .ς) ([res : (Pairof .rt/κ (Option .F)) seens]
                                         #:when (false? (cdr res)))
                     #;(printf "Function: ~a~n~n" (show-U σ f))
                     #;(printf "Seen, new~n")
                     (match-let* ([(cons (.rt/κ σ0 _ Vx0) _) res]
                                  #;[_ (printf "Old:~n~a~n~n" #;(cons Vx0 σ0) (show-V σ0 Vx0))]
                                  #;[_ (printf "New:~n~a~n~n" #;(cons Vx σ) (show-V σ Vx))]
                                  [(cons σ1 Vx1) (⊕ σ0 Vx0 σ Vx)])
                       #;(printf "Approx:~n~a~n~n" #;(cons Vx1 σ1) (show-V σ1 Vx1))
                       (.ς (.↓ e (ρ++ ρ Vx1)) σ1 (cons (.rt/κ σ1 f Vx1) k))))
                   (.ς (.↓ e (ρ++ ρ Vx)) σ (cons (.rt/κ σ f Vx) k))))
                (.ς (.blm l 'Λ (Prim (length Vx)) (arity=/C n)) σ k))]
        [#t (if (>= (length Vx) (- n 1)) ; FIXME varargs not handled yet
                (.ς (.↓ e (ρ++ ρ Vx (- n 1))) σ k)
                (.ς (.blm l 'Λ (Prim (length Vx)) (arity≥/C (- n 1))) σ k))])))
  
  (: step-@ : .V (Listof .V) Sym .σ .κ* → .ς*)
  (define (step-@ Vf V* l σ k)
    #;(printf "step-@:~n~a~n~a~n~n" (show-Ans σ Vf) (map (curry show-E σ) V*)) ;TODO reenable
    #;(printf "step-@:~nσ:~n~a~nf:~n~a~nx:~n~a~n~n" σ Vf V*)
    (match Vf
      [(.// U C*)
       (match U
         [(? .o? o) (match/nd (dbg/off '@ (δ σ o V* l)) [(cons σa A) (.ς A σa k)])]
         [(? .λ↓? f) (step-β f V* l σ k)]
         [(.Ar (.// (.Λ/C C* D v?) _) Vg (and l^3 (list _ _ lo)))
          (let* ([V# (length V*)]
                 [C# (length C*)]
                 [n (if v? (- C# 1) #f)])
            (if (if v? (>= V# (- C# 1)) (= V# C#))
                (.ς Vg σ (cons (.indy/κ C* V* '() D n l^3) k))
                (.ς (.blm l lo (Prim (length V*))(if v? (arity≥/C (- C# 1)) (arity=/C C#))) σ k)))]
         [_
          (match/nd (δ σ (.proc?) (list Vf) 'Λ)
            [(cons σt (.// (.b #t) _)) (error "impossible" (show-V σ Vf))]
            [(cons σf (.// (.b #f) _)) (.ς (.blm l 'Λ Vf PROC/C) σf k)])])]
      [(and L (.L i))
       (match/nd (δ σ (.proc?) (list L) 'Λ)
         [(cons σt (.// (.b #t) _))
          (match/nd (δ σt (.arity-includes?) (list L (Prim (length V*))) 'Λ)
            [(cons σt (.// (.b #t) _))
             (match (σ@ σt i)
               [(and V (or (.// (? .λ↓?) _) (.// (? .Ar?) _))) (step-@ V V* l σt k)]
               [(? .μ/V? Vf)
                (let ([seens (μs-seen k σt Vf V*)])
                  (or
                   (for/or: : (U #f .ς+) ([seen seens] #:when (hash? seen))
                     #;(printf "case 1~n") ∅)
                   (for/or: : (U #f .ς*) ([seen seens] #:when (cons? seen))
                     (match-let* ([(cons σ0 Vx0) seen]
                                  [(cons σi Vxi) (⊕ σ0 Vx0 σt V*)])
                       (match/nd: (.V → .ς) (unroll Vf)
                         [Vj (match-let ([(cons σi′ Vj) (alloc σi Vj)])
                               #;(printf "case 2~n")
                               (step-@ Vj Vxi l σi′ (cons (.μ/κ Vf Vxi σi) k)))])))
                   (match/nd: (.V → .ς) (unroll Vf)
                     [Vj (match-let ([(cons σi Vj) (alloc σt Vj)])
                           #;(printf "case 3~n")
                           #;(printf "0: ~a~n1: ~a~n~n" (show-V σ0 Vx0) (show-V σt V*))
                           (step-@ Vj V* l σi (cons (.μ/κ Vf V* σt) k)))])))]
               [_
                (match-let ([havocs (for/fold: ([s : (Setof .ς) ∅]) ([V V*])
                                      (set-union s (havoc V σt k)))]
                            [(cons σ′ La) (σ+ σt)])
                  (set-add havocs (.ς La σ′ k)))])]
            [(cons σf (.// (.b #f) _)) (.ς (.blm l 'Λ Vf (arity-includes/C (length V*))) σf k)])]
         [(cons σf (.// (.b #f) _)) (.ς (.blm l 'Λ Vf PROC/C) σf k)])]
      #;[(? .μ/V? Vf) (match/nd: (.V → .ς) (unroll Vf)
                        [Vf (step-@ Vf V* l σ k)])]))
  
  (: step-fc : .V .V Sym .σ .κ* → .ς*)
  (define (step-fc C V l σ k)
    (match (⊢ σ V C)
      ['Proved (.ς TT σ k)]
      ['Refuted (.ς FF σ k)]
      ['Neither
       (match C
         [(.// U D*)
          (match U
            [(and (.μ/C x C′) U)
             (cond
               [(chk-seen? k U (V-abs σ V)) (match-let ([(cons σ′ _) (refine σ V C)])
                                              (.ς TT σ′ k))]
               [else (match-let ([(cons σt _) (refine σ V C)]
                                 [(cons σf _) (refine σ V (.¬/C C))])
                       {set (.ς TT σt k) (.ς FF σf k)})])]
            [(.St 'and/c (list C1 C2)) (and/ς (list (.FC C1 V l) (.FC C2 V l)) σ k)]
            [(.St 'or/c (list C1 C2)) (or/ς (list (.FC C1 V l) (.FC C2 V l)) σ k)]
            [(.St '¬/c (list C′)) (.ς (.FC C′ V l) σ (cons (.@/κ '() (list (Prim 'not)) l) k))]
            [(.St/C t C*)
             (match/nd (δ σ (.st-p t (length C*)) (list V) l)
               [(cons σt (.// (.b #t) _))
                (match-let ([(.// (.St t V*) _) (σ@ σt V)])
                  (and/ς (for/list ([Vi V*] [Ci C*]) (.FC Ci Vi l)) σ k))]
               [(cons σf (.// (.b #f) _)) (.ς FF σf k)])]
            [_ (step-@ C (list V) l σ k)])]
         [(.L _) (step-@ C (list V) l σ k)])]))
  
  (: step-▹ : .V .V Sym^3 .σ .κ* → .ς*)
  (define (step-▹ C V l^3 σ k)
    #;(printf "Mon:~nC:~a~nV:~a~nσ:~a~nk:~a~n~n" C V σ k)
    (match-let ([(list l+ l- lo) l^3])
      (match (⊢ σ V C) ; want a check here to reduce redundant cases for recursive contracts
        ['Proved (.ς V σ k)]
        ['Refuted (.ς (.blm l+ lo V C) σ k)]
        ['Neither
         (match C
           [(.L i) ; FIXME this is wrong, need to take care of higher-order contract
            (match-let ([(cons σt Vt) (refine σ V C)]
                        [(cons σf Vf) (refine σ V (.¬/C C))])
              {set (.ς Vt σt k) (.ς Vf σf k)})]
           [(.// Uc C*)
            (match Uc
              [(and (.μ/C x C′) Uc)
               (cond
                 [(chk-seen? k Uc (V-abs σ V))
                  (match-let ([(cons σ′ V′) (dbg/off 'ho (refine σ V C))])
                    (.ς V′ σ′ k))]
                 ; hack to speed things up
                 [(flat/C? σ C)
                  #;(printf "Abt to refine:~nσ:~n~a~nV:~n~a~nC:~n~a~n~n" σ V C)
                  (match-let ([(cons σt Vt) (refine σ V C)]
                                            [(cons σf _) (refine σ V (.¬/C C))])
                                  {set (.ς Vt σt k) (.ς (.blm l+ lo V C) σf k)})]
                 [else (.ς V σ (list* (.▹/κ (cons (unroll/C Uc) #f) l^3) (.recchk/κ Uc (V-abs σ V)) k))])]
              [(.St 'and/c (list Dl Dr)) (.ς V σ (▹/κ1 Dl l^3 (▹/κ1 Dr l^3 k)))]
              [(.St 'or/c (list Dl Dr))
               (.ς (.FC Dl V lo) σ (cons (.if/κ (.Assume V Dl) (.Mon Dr V l^3)) k))]
              [(.St '¬/c (list D))
               (.ς (.FC D V lo) σ (cons (.if/κ (.blm l+ lo V C) (.Assume V C)) k))]
              [(.St/C t C*)
               (let ([n (length C*)])
                 (match/nd (δ σ (.st-p t n) (list V) lo)
                   [(cons σt (.// (.b #t) _))
                    (match-let ([(.// (.St t V*) _) (dbg/off '▹ (σ@ σt V))])
                      (.ς (→V (.st-mk t n)) σt
                          (cons (.@/κ (for/list ([C C*] [V V*]) (.Mon C V l^3)) '() lo) k)))]
                   [(cons σf (.// (.b #f) _)) (.ς (.blm l+ lo V (→V (.st-p t n))) σf k)]))]
              [(and Uc (.Λ/C Cx* D v?))
               (match/nd (δ σ (.proc?) (list V) lo)
                 [(cons σt (.// (.b #t) _))
                  (match v?
                    [#f (match/nd (δ σt (.arity-includes?) (list V (Prim (length Cx*))) lo)
                          [(cons σt (.// (.b #t) _)) (.ς (→V (.Ar C V l^3)) σt k)]
                          [(cons σf (.// (.b #f) _)) (.ς (.blm l+ lo V (arity-includes/C (length Cx*))) σf k)])]
                    [#t (match/nd (δ σt (.arity≥?) (list V (Prim (- (length Cx*) 1))) lo)
                          [(cons σt (.// (.b #t) _)) (.ς (→V (.Ar C V l^3)) σt k)]
                          [(cons σf (.// (.b #f) _)) (.ς (.blm l+ lo V (arity≥/C (- (length Cx*) 1))) σf k)])])]
                 [(cons σf (.// (.b #f) _)) (.ς (.blm l+ lo V PROC/C) σf k)])]
              [_ (.ς (.FC C V lo) σ (cons (.if/κ (.Assume V C) (.blm l+ lo V C)) k))])])])))
  
  (: step-E : .E .σ .κ* → .ς*)
  (define (step-E E σ k)
    #;(printf "E: ~a~n~n" E)
    (match E
      [(.↓ e ρ)
       (match e
         [(.•) (match-let ([(cons σ′ L) (σ+ σ)]) (.ς L σ′ k))]
         [(? .v? v) (.ς (close v ρ) σ k)]
         [(.x sd) (when (.X/V? (ρ@ ρ sd)) (error "STOP!"))(.ς (ρ@ ρ sd) σ k)]
         [(.x/c x) (.ς (ρ@ ρ x) σ k)]
         [(.ref name ctx ctx) (.ς (.↓ (ref-e ctx name) ρ∅) σ k)]
         [(.ref name in ctx)
          (.ς (.↓ (ref-c in name) ρ∅) σ
              (cons (.▹/κ  (cons #f (.↓ (ref-e in name) ρ∅)) (list in ctx in)) k))]
         [(.@ f xs l) (.ς (.↓ f ρ) σ (cons (.@/κ (for/list ([x xs]) (.↓ x ρ)) '() l) k))]
         [(.@-havoc x)
          (match/nd: (.V → .ς) (match (ρ@ ρ x)
                                 [(? .//? V) V]
                                 [(.L i) (match (σ@ σ i) ; TODO rewrite
                                           [(? .//? V) V]
                                           [(? .μ/V? V) (unroll V)])]
                                 [(? .μ/V? V) (unroll V)])
            [(and V (.// U C*))
             ; always alloc the result of unroll
             ; FIXME: rewrite 'unroll' to force it
             (match-let ([(cons σ V) (alloc σ V)])
               #;(printf "havoc: ~a~n~n" (show-V σ V))
               (match U
                 [(.λ↓ (.λ n _ _) _)
                  #;(printf "case1: ~a~n~n" (show-E σ V))
                  (match-let ([(cons σ′ Ls) (σ++ σ n)])
                    (step-@ V Ls '☠ σ′ k))]
                 [(.Ar (.// (.Λ/C Cx _ _) _) _ _)
                  #;(printf "case2: ~a~n~n" (show-E σ V))
                  (match-let ([(cons σ′ Ls) (σ++ σ (length Cx))])
                    (step-@ V Ls '☠ σ′ k))]
                 [_ ∅]))]
            [X (error "weird" X)])]
         #;[(.apply f xs l) (.ς (.↓ f ρ) σ (cons (.apply/ar/κ (.↓ xs ρ) l) k))]
         [(.if i t e) (.ς (.↓ i ρ) σ (cons (.if/κ (.↓ t ρ) (.↓ e ρ)) k))]
         [(.amb e*) (for/set: .ς ([e e*]) (.ς (.↓ e ρ) σ k))]
         [(.μ/c x e) (.ς (.↓ e (ρ+ ρ x (→V (.X/C x)))) σ (cons (.μc/κ x) k))]
         [(.λ/c '() d v?) (.ς (→V (.Λ/C '() (.↓ d ρ) v?)) σ k)]
         [(.λ/c (cons c c*) d v?) (.ς (.↓ c ρ) σ (cons (.λc/κ c* '() d ρ v?) k))]
         [(.struct/c t '()) (.ς (→V (.st-p t 0)) σ k)]
         [(.struct/c t (cons c c*)) (.ς (.↓ c ρ) σ (cons (.structc/κ t c* ρ '()) k))])]
      [(.Mon C E l^3) (.ς C σ (cons (.▹/κ (cons #f E) l^3) k))]
      [(.FC C V l) (step-fc C V l σ k)]
      [(.Assume V C) (match-let ([(cons σ′ V′) (refine σ V C)]) (.ς V′ σ′ k))]))
  
  (: step-V : .V .σ .κ .κ* → .ς*)
  (define (step-V V σ κ k)
    (match κ
      [(.if/κ E1 E2) (match/nd (δ σ .false/c (list V) 'Λ)
                       [(cons σt (.// (.b #f) _)) (.ς E1 σt k)]
                       [(cons σf (.// (.b #t) _)) (.ς E2 σf k)])]
      
      [(.@/κ (cons E1 Er) V* l) (.ς E1 σ (cons (.@/κ Er (cons V V*) l) k))]
      [(.@/κ '() V* l) (match-let ([(cons Vf Vx*) (reverse (cons V V*))])
                         (step-@ Vf Vx* l σ k))]
      
      #;[(.apply/ar/κ E l) (.ς E σ (cons (.apply/fn/κ V l) k))]
      #;[(.apply/fn/κ Vf l) (step-apply Vf V l σ k)]
      
      [(.▹/κ (cons #f (? .E? E)) l^3) (.ς E σ (cons (.▹/κ (cons V #f) l^3) k))]
      [(.▹/κ (cons (? .V? C) #f) l^3) (step-▹ C V l^3 σ k)]
      
      [(.rt/κ _ _ _) (.ς V σ k)]
      [(.recchk/κ _ _) (.ς V σ k)]
      [(.μ/κ _ _ _) (.ς V σ k)]
      
      ;; indy
      [(.indy/κ (list Ci) (cons Vi Vr) Vs↓ D n l^3) ; repeat last contract, handling var-args
       (step-▹ Ci Vi (¬l l^3) σ (cons (.indy/κ (list Ci) Vr (cons V Vs↓) D n l^3) k))]
      [(.indy/κ (cons Ci Cr) (cons Vi Vr) Vs↓ D n l^3)
       (step-▹ Ci Vi (¬l l^3) σ (cons (.indy/κ Cr Vr (cons V Vs↓) D n l^3) k))]
      [(.indy/κ _ '() Vs↓ (.↓ d ρ) n l^3) ; evaluate range contract
       (match-let ([(and V* (cons Vf Vx*)) (reverse (cons V Vs↓))])
         (.ς (.↓ d (ρ++ ρ Vx* n)) σ (cons (.indy/κ '() '() V* #f n l^3) k)))]
      [(.indy/κ _ '() (cons Vf Vx) #f _ (and l^3 (list l+ _ _))) ; apply inner function
       #;(printf "range: ~a~n~n" (show-E σ V))
       (step-@ Vf Vx l+ σ (▹/κ1 V l^3 k))]
      
      ; contracts
      [(.μc/κ x) (.ς (→V (.μ/C x V)) σ k)]
      [(.λc/κ '() c↓ d ρ v?) (.ς (→V (.Λ/C (reverse (cons V c↓)) (.↓ d ρ) v?)) σ k)]
      [(.λc/κ (cons c c*) c↓ d ρ v?) (.ς (.↓ c ρ) σ (cons (.λc/κ c* (cons V c↓) d ρ v?) k))]
      [(.structc/κ t '() _ c↓) (.ς (→V (.St/C t (reverse (cons V c↓)))) σ k)]
      [(.structc/κ t (cons c c*) ρ c↓) (.ς (.↓ c ρ) σ (cons (.structc/κ t c* ρ (cons V c↓)) k))]))
  
  (match-lambda
    [(.ς (? .V? V) σ (cons κ k))
     (when (match? V (.// (.•) _))
       (printf "~a~n~n" (show-ς (.ς V σ (cons κ k))))
       (error "impossible"))
     (step-V V σ κ k)]
    [(.ς (? .E? E) σ k) (step-E E σ k)]))

(: and/ς : (Listof .E) .σ .κ* → .ς)
(define (and/ς E* σ k)
  (match E*
    ['() (.ς TT σ k)]
    [(list E) (.ς E σ k)]
    [(cons E Er) (.ς E σ (foldr (λ: ([Ei : .E] [k : .κ*]) (cons (.if/κ Ei FF) k)) k Er))]))

(: or/ς : (Listof .E) .σ .κ* → .ς)
(define (or/ς E* σ k)
  (match E*
    ['() (.ς FF σ k)]
    [(list E) (.ς E σ k)]
    [(cons E Er) (.ς E σ (foldr (λ: ([Ei : .E] [k : .κ*]) (cons (.if/κ TT Ei) k)) k Er))]))

#;(: wrap : .Λ/C .V Sym^3 → .V)
#;(define (wrap C V l^3)
    (match V
      [(.// (.Ar (.// (.Λ/C Cx D v?) _) V′ (list l+ l- l)) D*)
       (match-let ([(.Λ/C Cz D′ v?′) C]
                   [(list h+ h- h) l^3])
         (if (and (equal? Cx Cz) (equal? D D′) (equal? v? v?′) (eq? l h))
             (.// (.Ar (→V (.Λ/C Cz D v?)) V′ (list l+ h- l)) D*)
             (→V (.Ar (→V C) V l^3))))]
      [_ (→V (.Ar (→V C) V l^3))]))

(: ▹/κ1 : .V Sym^3 .κ* → .κ*)
(define (▹/κ1 C l^3 k)
  (match C
    [(.// (.λ↓ (.λ 1 (.b #t) _) _) _) k]
    [(.// (? .Λ/C?) _) (cons (.▹/κ (cons C #f) l^3) k)]
    [_ (cons (.▹/κ (cons C #f) l^3)
             (let: trim : .κ* ([k : .κ* k])
               (match k
                 [(cons (and κ (.▹/κ (cons (? .V? D) #f) _)) kr)
                  (match (C⇒C C D)
                    ['Proved (trim kr)]
                    [_ (cons κ (trim kr))])]
                 [_ k])))]))

(: apps-seen : .κ* .σ .λ↓ (Listof .V) → (Listof (Pairof .rt/κ (Option .F))))
(define (apps-seen k σ f Vx)
  #;(printf "apps-seen~nf: ~a~nk: ~a~n~n" (show-V σ∅ (→V f)) (show-k σ∅ k))
  (for/fold: ([acc : (Listof (Pairof .rt/κ (Option .F))) '()]) ([κ k])
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
  #;(printf "apps-seen~nf: ~a~nk: ~a~n~n" (show-V σ∅ (→V f)) (show-k σ∅ k))
  (for/fold: ([acc : (Listof (U .F (Pairof .σ (Listof .V)))) '()]) ([κ k])
    (match κ
      [(.μ/κ g Vx0 σ0) (match ((⊑ σ σ0) Vx Vx0)
                         [#f (cons (ann (cons σ0 Vx0) (Pairof .σ (Listof .V))) acc)]
                         [(? hash? F) (cons F acc)])]
      [_ acc])))

(: split-κ* : .rt/κ .κ* → (Pairof .κ* .κ*))
(define (split-κ* κ k)
  #;(printf "Split:~n~a~n~n~a~n~n" κ k)
  (let: go ([l : .κ* '()] [k k])
    (match k
      ['() (error "WTF")]
      [(cons (? .rt/κ? κ′) kr)
       (if (equal? κ κ′) (cons (reverse l) kr) (go (cons κ′ l) kr))]
      [(cons κ kr) (go (cons κ l) kr)])))

;;;;; small programs for testing
(define f
  (read-p
   `((module f
       (provide [f (int? . -> . int?)])
       (define (f n)
         (if (= n 0) 1 (* n (f (- n 1))))))
     (require f)
     (f 100))))

(: chk-seen? : .κ* .μ/C .V → Bool)
(define (chk-seen? k C V)
  (for/or: ([κ k] #:when (match? κ (? .recchk/κ?)))
    (match-let ([(.recchk/κ C′ V′) κ])
      (and (equal? C′ C) (equal? V′ V)))))

;; for debugging
(define (e x) (set->list (ev (read-p x))))

(: show-k : .σ .κ* → (Listof Any))
(define (show-k σ k) (for/list ([κ k]) (show-κ σ κ)))

(: show-κ : .σ .κ → Any)
(define (show-κ σ κ)
  (define E (curry show-E σ))
  (match κ
    [(.if/κ t e) `(if ∘ ,(E t) ,(E e))]
    [(.@/κ e* v* _) `(@ ,@(reverse (map E v*)) ∘ ,@(map E e*))]
    #;[(.apply/fn/κ Vf _) `(apply ,(E Vf) ∘)]
    #;[(.apply/ar/κ Ex _) `(apply ∘ ,(E Ex))]
    [(.▹/κ (cons #f (? .E? e)) _) `(∘ ▹ ,(E e))]
    [(.▹/κ (cons (? .E? C) #f) _) `(,(E C) ▹ ∘)]
    [(.indy/κ Cs xs xs↓ d _ _) `(indy ,(map E Cs) ,(map E xs) ,(map E xs↓)
                                      ,(match d [#f '_] [(? .E? d) (E d)]))]
    [(.μc/κ x) `(μ/c ,x ∘)]
    [(.λc/κ cs Cs d ρ _) `(λ/c (,@(reverse (map E Cs)) ,@(map show-e cs)) ,(show-e d))]
    [(.structc/κ t c _ c↓) `(struct/c ,t (,@(reverse (map E c↓)) ,(map show-e c)))]
    [(.rt/κ _ f x) `(rt ,(E (→V f)) ,@(map E x))]
    [(.blr/κ _ _ V) `(blr ,(E V))]
    [(.recchk/κ c v) `(μ/▹ ,(E (→V c)) ,(E v))]))

(: show-ς : .ς → Any)
(define show-ς
  (match-lambda
    [(.ς E σ k) `((E: ,(if (.E? E) (show-E σ E) (show-κ σ (car E))))
                  (σ: ,@(show-σ σ))
                  (k: ,@(show-k σ k)))]))

; rename all labels to some canonnical form based on the expression's shape
; relax, this only happens a few times, not that expensive
(: canon : .ς → .ς)
(define (canon ς)
  (match-define (.ς (? .E? E) σ k) ς)
  (define F F∅)
  (: alloc! : Int → Int)
  (define (alloc! i)
    (match (hash-ref F i #f)
      [(? int? j) j]
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
      [(.ρ m l) (.ρ (for/fold: ([m′ : (Map (U Int Sym) .V) m∅]) ([i (in-hash-keys m)])
                      (hash-set m′ i (go! (hash-ref m i))))
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
  
  (: fixup : (case→ [.V → .V] [.↓ → .↓] [.E → .E]
                  [.μ/C → .μ/C] [.λ↓ → .λ↓] [.U → .U] [.ρ → .ρ] [.κ → .κ] [.κ* → .κ*]
                  [(Listof .V) → (Listof .V)] [(Listof .E) → (Listof .E)]
                  [.σ → .σ]))
  (define (fixup x)
    (match x
      ; E
      [(.↓ e ρ) (.↓ e (fixup ρ))]
      [(.FC c v l) (.FC (fixup c) (fixup v) l)]
      [(.Mon c e l) (.Mon (fixup c) (fixup e) l)]
      [(.Assume v c) (.Assume (fixup v) (fixup c))]
      [(.blm f g v c)(.blm f g (fixup v) (fixup c))]
      ; V
      [(? .L? x) x]
      [(.// U C*) (.// (fixup U) (subst/L C* F))]
      [(.μ/V x V*) (.μ/V x (subst/L V* F))]
      [(? .X/V? x) x]
      ; U
      [(.Ar c v l) (.Ar (fixup c) (fixup v) l)]
      [(.St t V*) (.St t (fixup V*))]
      [(.λ↓ f ρ) (.λ↓ f (fixup ρ))]
      [(.Λ/C c d v?) (.Λ/C (fixup c) (fixup d) v?)]
      [(.St/C t V*) (.St/C t (fixup V*))]
      [(.μ/C x c) (.μ/C x (fixup c))]
      [(? .X/C? x) x]
      [(? .prim? p) p]
      ; ρ
      [(.ρ m l) (.ρ (for/fold: ([m′ : (Map (U Int Sym) .V) m∅]) ([i (in-hash-keys m)])
                      (hash-set m′ i (fixup (hash-ref m i))))
                    l)]
      ; κ
      [(.if/κ t e) (.if/κ (fixup t) (fixup e))]
      [(.@/κ e* v* l) (.@/κ (fixup e*) (fixup v*) l)]
      [(.▹/κ (cons C E) l)
       (.▹/κ (cond [(and (false? C) (.E? E)) (cons #f (fixup E))]
                   [(and (.V? C) (false? E)) (cons (fixup C) #f)]
                   [else (error "impossible!")])
             l)]
      [(.indy/κ c x x↓ d v? l)
       (.indy/κ (fixup c) (fixup x) (fixup x↓) (if (.↓? d) (fixup d) #f) v? l)]
      [(? .μc/κ? x) x]
      [(.λc/κ c c↓ d ρ v?) (.λc/κ c (fixup c↓) d (fixup ρ) v?)]
      [(.structc/κ t c ρ c↓) (.structc/κ t c (fixup ρ) (fixup c↓))]
      #;[(.rt/κ σ f x) (.rt/κ (fixup σ) (fixup f) (fixup x))]
      #;[(.blr/κ G σ V) (.blr/κ G (fixup σ) (fixup V))]
      #;[(.recchk/κ C V) (.recchk/κ (fixup C) (fixup V))]
      [(.μ/κ f xs σ) (.μ/κ f (fixup xs) (fixup σ))]
      ; σ
      [(.σ m _)
       #;(printf "F: ~a~nm: ~a~n~n" F m)
       (match-let ([(cons σ′ _) (σ++ σ∅ (hash-count F))])
                  (for/fold: ([σ′ : .σ σ′]) ([i (in-hash-keys F)])
                    (match (hash-ref m i #f)
                      [(? .V? Vi) (σ-set σ′ (hash-ref F i) (subst/L Vi F))]
                      [#f σ′])))]
      [(? list? l) (map fixup l)]))
  
  (let* ([E′ (go! E)]
         [k′ (go! k)])
    (.ς (fixup E′) (fixup σ) (fixup k′))))
