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
  (.rt/κ [f : .λ↓] [x : (Listof .V)]) ; where all labels are fully resolved
  (.blr/κ [old : .V])
  (.recchk/κ [c : .μ/C] [v : .V])) ; where all labels are fully resolved
(define-type .κ* (Listof .κ))

; #f in e's position is for pending states
(struct: .ς ([e : (U .rt/κ .E)] [s : .σ] [k : .κ*]) #:transparent)
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

(: ev : .p → .ς+)
(define (ev p)
  (match-define (.p (and m* (.m* _ ms)) e) p)
  (define step (step-p m*))
  (define: Ξ : (MMap .rt/κ (List .σ .κ* .κ*)) (make-hash))
  (define: M : (MMap .rt/κ .V) (make-hash))
  
  (: Ξ+! : .rt/κ .σ .κ* .κ* → Void)
  (define (Ξ+! ctx σ l r)
    #;(printf "Ξ[~a] += ~a~n~n"
            (show-κ σ ctx)
            `((σ: ,@(show-σ σ))
              (l: ,@(show-k σ l))
              (r: ,@(show-k σ r))))
    (dbg/off 'Ξ+! (mmap-join! Ξ ctx (list σ l r))))
  
  (: M+! : .rt/κ .V → Void)
  (define (M+! ctx V^)    
    (let* ([V* (hash-ref M ctx (λ () ∅))]
           [del (for/fold: ([del : (Setof .V) ∅]) ([Vi V*])
                  (cond
                    [(equal? Vi V^) del]
                    [(⊑ Vi V^) (set-add del Vi)]
                    [(⊑ V^ Vi) (set-add del V^)]
                    [else del]))])
      (hash-set! M ctx (set-subtract (set-add V* V^) del))))
  
  (: upd-M! : .rt/κ .V .V → Void)
  (define (upd-M! ctx V0 V^)
    (hash-update! M ctx (λ: ([s : (Setof .V)]) (set-add (set-remove s V0) V^))))
  
  (: Ξ@ : .rt/κ → (Setof (List .σ .κ* .κ*)))
  (define (Ξ@ ctx) (hash-ref Ξ ctx (λ () ∅)))
  
  (: M@ : .rt/κ → (Setof .V))
  (define (M@ ctx) (hash-ref M ctx (λ () ∅)))
  
  (: m-opaque? : Sym → Bool)
  (define (m-opaque? x) ; TODO: profile, see if this is worth memoizing
    (match-let ([(.m _ defs) (hash-ref ms x)])
      (for/or ([d (in-hash-values defs)] #:when (match? d (cons (.•) _))) #t)))
  
  (: step* : .ς → .ς+)
  (define (step* ς)
    (define: ans : .ς+ ∅)
    (define: seen : .ς+ ∅)
    
    (define-syntax-rule (when-unseen! ς e ...)
      (let ([x ς]) ; only need to keep around one class of states
        (if (.V? (.ς-e x))
            (let ([x^ (match x
                        [(.ς Vn σ (cons (.@/κ '() _ _) _)) (ς-abs x)]
                        [_ x])])
              #;(printf "~a~nabs:~n~a~n~n" x x^)
              (unless (set-member? seen x^)
                (set! seen (set-add seen x^))
                e ...))
            (begin e ...))))
    
    (: resume : .V .rt/κ .σ .κ* .κ* → Void)
    (define (resume V^ ctx σ l r)
      (let ([k^ (append l (list* (.blr/κ V^) ctx r))])
        (when-unseen! (.ς V^ σ k^)
                      (match-let ([(cons σ′ V) (alloc σ V^)])
                        #;(printf "resumed with V = ~a~n~n" (show-Ans σ′ V))
                        (visit (dbg/off 'resume (.ς V σ′ k^)))))))
    
    ; imperative DFS speeds interpreter up by ~40%
    ; from not maintaining an explicit frontier set
    (: visit : .ς → Void)
    (define (visit ς)
      #;(printf "~a~n~n" (show-ς ς))
      #;(when (match? (.ς-k ς) (cons (? .blr/κ?) (cons (not (? .rt/κ?)) _))) (error "STOP"))
      (match ς
        ; record final states, omit blames on top, havoc, and opaque modules
        [(? final? ς) 
         #;(printf "------~n~n")
         (unless (match? ς (.ς [.blm (or '† '☠ (? m-opaque?)) _ _ _] _ _))
           (set! ans (set-add ans ς)))]
        ; remember waiting contexts and plug any available answers into it
        [(.ς (and ctx (.rt/κ f Vx)) σ k)
         (match-let ([(cons l r) (split-κ* ctx k)])
           (Ξ+! ctx σ l r)
           (for ([V^ (M@ ctx)])
             #;(printf "From Ξ, resume with~nK = ~a~n~nand V^ = ~a~n~n"
                     `((σ: ,@(show-σ σ))
                       (l: ,@(show-k σ l))
                       (r: ,@(show-k σ r)))
                     (show-E σ V^))
             (dbg/off 'res/Ξ (resume V^ ctx σ l r))))]
        ; remember returned value and return to any other waiting contexts
        [(.ς (? .V? V) σ (cons (? .rt/κ? ctx) k))
         (let ([V^ (V-abs σ V)])
           (dbg/off 'M+!/M (M+! ctx V^))
           #;(printf "M[~a] = {~a}~n~n"
                   (show-κ σ ctx)
                   (for/list: : (Listof Any) ([V (hash-ref M ctx)]) (show-E σ V)))
           (for: ([K : (List .σ .κ* .κ*) (Ξ@ ctx)])             
             (match-let ([(list σ l r) K])
               #;(printf "From M, resume with~nK = ~a~n~nand V^ = ~a~n~n"
                       `((σ: ,@(show-σ σ))
                         (l: ,@(show-k σ l))
                         (r: ,@(show-k σ r)))
                       (show-E σ V^))
               (dbg/off 'res/M (resume V^ ctx σ l r)))))
         (visit (.ς V σ k))]
        ; blur value in M table ; TODO: this is a hack
        [(.ς (? .V? V) σ (cons (.blr/κ V0) (cons (? .rt/κ? ctx) k)))
         (let ([V^ (⊕ V0 (V-abs σ V))])
           (upd-M! ctx V0 V^)
           #;(printf "M: ~a  ⊕  ~a  =  ~a~n~n" (show-V σ V0) (show-V σ (V-abs σ V)) (show-V σ V^))
           #;(printf "M[~a] = {~a}~n~n"
                   (show-κ σ ctx)
                   (for/list: : (Listof Any) ([V (hash-ref M ctx)]) (show-E σ V)))
           (for: ([K : (List .σ .κ* .κ*) (Ξ@ ctx)])
             (match-let ([(list σ l r) K])
               #;(printf "From M (blur), resume with~nK = ~a~n~nand V^ = ~a~n~n"
                       `((σ: ,@(show-σ σ))
                         (l: ,@(show-k σ l))
                         (r: ,@(show-k σ r)))
                       (show-E σ V^))
               (dbg/off 'res/M (resume V^ ctx σ l r)))))
         (visit (.ς V σ k))]
        [(.ς (? .V? V) σ (cons (.blr/κ V1) (cons (.blr/κ V0) k)))
         #;(printf "B: ~a  ⊕  ~a  =  ~a~n~n" (show-V σ V0) (show-V σ V1) (show-V σ (⊕ V0 V1)))
         #;(printf "Blur: ~a with ~a~n~n" (show-E σ V0) (show-E σ V1))
         (visit (.ς V σ (cons (.blr/κ (⊕ V0 V1)) k)))] ; FIXME HACK
        ; do regular 1-step on unseen state
        [_ (match (dbg/off 'step (step ς))
             [(? set? s) #;(printf "SPLIT ~a~n~n" (set-count s))
                         (for ([ςi s]) #;(printf "BRANCH:~n~n") (when-unseen! ςi (visit ςi)))]
             [(? .ς? ςi) (when-unseen! ςi (visit ςi))])]))
    
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
  
  (: ref-v : Sym Sym → .e)
  (define (ref-v m x)
    (match-let ([(.m _ defs) (hash-ref ms m)])
      (car (hash-ref defs x))))
  
  (: ref-c : Sym Sym → .e)
  (define (ref-c m x)
    (match-let ([(.m _ decs) (hash-ref ms m)])
      (match (cdr (hash-ref decs x))
        [(? .e? c) c]
        [_ (error (format "module ~a does not export ~a" m x))])))
  
  (define HAVOC (match-let ([(? .λ? v) (ref-v '☠ 'havoc)]) (.λ↓ v ρ∅)))
  
  ; promote havoc to meta-language level to reduce excessive splits
  ; in the presence of lots of struct declaration
  (: havoc : .V .σ .κ* → .ς+)
  (define (havoc V σ k)
    (define-set: ac : .ς [_ add!])
    
    (: havoc1! : .V → Void)
    (define (havoc1! V)
      (match-let ([(cons σ′ L) (σ+ σ)])
        (add! (step-@ V (list L) '☠ σ′ k))))
    
    (let: go : Void ([V V])
      (match V
        [(.L i) (go (σ@ σ i))]
        [(.// (.St _ V*) _) (for ([V V*]) (go V))]
        [(or (.// (? .λ↓?) _) (.// (? .Ar?) _)) (havoc1! V)]
        [_ (void)]))
    ac)
  
  (: step-β : .λ↓ (Listof .V) Sym .σ .κ* → .ς)
  (define (step-β f V* l σ k)
    (match-let* ([(.λ↓ (.λ n e v?) ρ) f]
                 [f^ (.λ↓ (.λ n e v?) (V-abs σ ρ))])
      (match v?
        [#f (if (= (length V*) n)
                (let ([V*^ (V-abs σ V*)])
                  (match (app-seen? k f^)
                    [#f (.ς (.↓ e (ρ++ ρ V*)) σ (cons (.rt/κ f^ V*^) k))]
                    [(? list? V0*)
                     (let* ([V1*^ (dbg/off 'x (⊕ V0* V*^))]
                            [ctx (.rt/κ f^ V1*^)])
                       #;(printf "X: ~a  ⊕  ~a  =  ~a~n~n" (map (curry show-Ans σ) V0*) (show-V σ V*^) (show-V σ V1*^))
                       (if (equal? V1*^ V0*) (.ς ctx σ k)
                           (match-let ([(cons σ′ V1*) (alloc σ V1*^)])
                             #;(printf "continue with~n~a~n~n" (map (curry σ@ σ′) V1*))
                             (.ς (.↓ e (ρ++ ρ V1*)) σ′ (cons ctx k)))))]))
                (.ς (.blm l 'Λ (Prim (length V*)) (arity=/C n)) σ k))]
        [#t (if (>= (length V*) (- n 1)) ; FIXME also insert rt frame here
                (.ς (.↓ e (ρ++ ρ V* (- n 1))) σ k)
                (.ς (.blm l 'Λ (Prim (length V*)) (arity≥/C (- n 1))) σ k))])))
  
  (: step-@ : .V (Listof .V) Sym .σ .κ* → .ς*)
  (define (step-@ Vf V* l σ k)
    #;(printf "step-@:~n~a~n~a~n~n" (show-Ans σ Vf) (map (curry show-E σ) V*))
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
            [(cons σt (.// (.b #t) _)) (error "impossible")]
            [(cons σf (.// (.b #f) _)) (.ς (.blm l 'Λ Vf PROC/C) σf k)])])]
      [(and L (.L i))
       (match/nd (δ σ (.proc?) (list L) 'Λ)
         [(cons σt (.// (.b #t) _))
          (match/nd (δ σt (.arity-includes?) (list L (Prim (length V*))) 'Λ)
            [(cons σt (.// (.b #t) _))
             (match (σ@ σt i)
               [(and V (or (.// (? .λ↓?) _) (.// (? .Ar?) _))) (step-@ V V* l σt k)]
               [(? .μ/V? V) (match/nd: (.V → .ς) (unroll V)
                             [V (match-let ([(cons σt V) (alloc σt V)])
                                  (step-@ V V* l σt k))])]
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
                 [(flat/C? σ C) (match-let ([(cons σt Vt) (refine σ V C)]
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
    (match E
      [(.↓ e ρ)
       (match e
         [(.•) (match-let ([(cons σ′ L) (σ+ σ)]) (.ς L σ′ k))]
         [(? .v? v) (.ς (close v ρ) σ k)]
         [(.x sd) (when (.X/V? (ρ@ ρ sd)) (error "STOP!"))(.ς (ρ@ ρ sd) σ k)]
         [(.x/c x) (.ς (ρ@ ρ x) σ k)]
         [(.ref name ctx ctx) (.ς (.↓ (ref-v ctx name) ρ∅) σ k)]
         [(.ref name in ctx)
          (.ς (.↓ (ref-c in name) ρ∅) σ
              (cons (.▹/κ  (cons #f (.↓ (ref-v in name) ρ∅)) (list in ctx in)) k))]
         [(.@ f xs l) (.ς (.↓ f ρ) σ (cons (.@/κ (for/list ([x xs]) (.↓ x ρ)) '() l) k))]
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
      
      [(.▹/κ (cons #f (? .E? E)) l^3) (.ς E σ (cons (.▹/κ (cons V #f) l^3) k))]
      [(.▹/κ (cons (? .V? C) #f) l^3) (step-▹ C V l^3 σ k)]
      
      [(.rt/κ _ _) (.ς V σ k)]
      [(.recchk/κ _ _) (.ς V σ k)]
      
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
    [(.ς (? .V? V) σ (cons κ k)) (when (match? V (.// (.•) _)) (error "impossible")) (step-V V σ κ k)]
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
    [_ (cons (.▹/κ (cons C #f) l^3)
             (let: trim : .κ* ([k : .κ* k])
               (match k
                 [(cons (and κ (.▹/κ (cons (? .V? D) #f) _)) kr)
                  (match (C⇒C C D)
                    ['Proved (trim kr)]
                    [_ (cons κ (trim kr))])]
                 [_ k])))]))

(: app-seen? : .κ* .λ↓ → (U #f (Listof .V)))
(define (app-seen? k f)
  (let go ([k k])
    (match k
      ['() #f]
      [(cons (.rt/κ g Vx) kr) (if (equal? g f) Vx (go kr))]
      [(cons _ kr) (go kr)])))

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

(: ≃ : (case→ [.σ .E .σ .E → Bool]
              [.σ .κ .σ .κ → Bool]
              [.σ .κ* .σ .κ* → Bool]
              [.σ (Listof .E) .σ (Listof .E) → Bool]
              [.σ .ρ .σ .ρ → Bool]
              [.σ .U .σ .U → Bool]))
(define (≃ σ0 x0 σ1 x1)
  (: go : (case→ [.E .E → Bool]
                 [.κ .κ → Bool]
                 [.κ* .κ* → Bool]
                 [(Listof .E) (Listof .E) → Bool]
                 [.ρ .ρ → Bool]
                 [.U .U → Bool]
                 [(Setof .V) (Setof .V) → Bool])) ; expensive, restricted
  (define (go x0 x1)
    (match* (x0 x1)
      ; κ*/E*
      [((? list? x0*) (? list? x1*))
       (let loop ([x0* x0*] [x1* x1*])
         (match* (x0* x1*)
           [('() '()) #t]
           [((cons x0 x0r) (cons x1 x1r)) (and (go x0 x1) (loop x0r x1r))]
           [(_ _) #f]))]
      [((? set? x0*) (? set? x1*)) ; only happens under μ, won't be that bad
       (and (= (set-count x0*) (set-count x1*))
            (for/and: : Bool ([x0 x0*])
              (for/or: : Bool ([x1 x1*])
                (go x0 x1))))]
      ; κ
      [((.if/κ E0t E1e) (.if/κ E0t E1e)) (and (go E0t E0t) (go E1e E1e))]
      [((.@/κ E0* V0* _) (.@/κ E1* V1* _)) (and (go E0* E1*) (go V0* V1*))]
      [((.▹/κ (cons C0 V0) _) (.▹/κ (cons C1 V1) _))
       (and (or (and (false? C0) (false? C1)) (and (.V? C0) (.V? C1) (go C0 C1)))
            (or (and (false? V0) (false? V1)) (and (.V? V0) (.V? V1) (go V0 V1))))]
      [((.indy/κ C0 V0 V0↓ D0 v? _) (.indy/κ C1 V1 V1↓ D1 v? _))
       (and (go C0 C1) (go V0 V1) (go V0↓ V1↓)
            (match* (D0 D1)
              [((.↓ e ρ0) (.↓ e ρ1)) (go ρ0 ρ1)]
              [(x y) (eq? x y)]))]
      [((.rt/κ f0 x0) (.rt/κ f1 x1)) (and (go f0 f1) (go x0 x1))]
      [((.blr/κ V0) (.blr/κ V1)) (go V0 V1)]
      [((.λc/κ c c0↓ d ρ0 v?) (.λc/κ c c1↓ d ρ1 v?)) (and (go c0↓ c1↓) (go ρ0 ρ1))]
      [((.structc/κ t c ρ0 c0↓) (.structc/κ t c ρ1 c1↓)) (and (go ρ0 ρ1) (go c0↓ c1↓))]
      ; E
      [((.↓ e ρ0) (.↓ e ρ1)) (go ρ0 ρ1)]
      [((.FC C0 V0 _) (.FC C1 V1 _)) (and (go C0 C1) (go V0 V1))]
      [((.Mon C0 E0 _) (.Mon C1 E1 _)) (and (go C0 C1) (go E0 E1))]
      [((.Assume V0 C0) (.Assume V1 C1)) (and (go C0 C1) (go V0 V1))]
      [((.L i) (.L j)) (if (eq? i j) #t (go (σ@ σ0 i) (σ@ σ1 j)))]
      [((.L i) V1) (go (σ@ σ0 i) V1)]
      [(V0 (.L i)) (go V0 (σ@ σ1 i))]
      [((.// U0 C0) (.// U1 C1)) (and (go U0 U1) (go C0 C1))]
      [((.μ/V x V0) (.μ/V x V1)) (go V0 V1)]
      ; U
      [((.Ar C0 V0 _) (.Ar C1 V1 _)) (and (go C0 C1) (go V0 V1))]
      [((.St t V0*) (.St t V1*)) (go V0* V1*)]
      [((.λ↓ f ρ0) (.λ↓ f ρ1)) (go ρ0 ρ1)]
      [((.Λ/C C0 D0 v?) (.Λ/C C1 D1 v?)) (and (go C0 C1) (go D0 D1))]
      [((.St/C t V0*) (.St/C t V1*)) (go V0* V1*)]
      [((.μ/C x C0) (.μ/C x C1)) (go C0 C1)]
      ; rest
      [(x y) (equal? x y)]))
  (go x0 x1))

(: chk-seen? : .κ* .μ/C .V → Bool)
(define (chk-seen? k C V)
  (let go ([k k])
    (match k
      ['() #f]
      [(cons (.recchk/κ C′ V′) kr) (or (and (equal? C′ C) (equal? V′ V)) (go kr))]
      [(cons _ kr) (go kr)])))

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
    [(.▹/κ (cons #f (? .E? e)) _) `(∘ ▹ ,(E e))]
    [(.▹/κ (cons (? .E? C) #f) _) `(,(E C) ▹ ∘)]
    [(.indy/κ Cs xs xs↓ d _ _) `(indy ,(map E Cs) ,(map E xs) ,(map E xs↓)
                                      ,(match d [#f '_] [(? .E? d) (E d)]))]
    [(.μc/κ x) `(μ/c ,x ∘)]
    [(.λc/κ cs Cs d ρ _) `(λ/c (,@(reverse (map E Cs)) ,@(map show-e cs)) ,(show-e d))]
    [(.structc/κ t c _ c↓) `(struct/c ,t (,@(reverse (map E c↓)) ,(map show-e c)))]
    [(.rt/κ f x) `(rt ,(E (→V f)) ,@(map E x))]
    [(.blr/κ V) `(blr ,(E V))]
    [(.recchk/κ c v) `(μ/▹ ,(E (→V c)) ,(E v))]))

(: show-ς : .ς → Any)
(define show-ς
  (match-lambda
    [(.ς E σ k) `((E: ,(if (.E? E) (show-E σ E) (show-κ σ E)))
                  (σ: ,@(show-σ σ))
                  (k: ,@(show-k σ k)))]))

(: ς-abs : .ς → .ς)
(define (ς-abs ς)
  (match-define (.ς (? .E? E) σ k) ς)
  (: go : (case→ [.V → .V] [.E → .E] [.ρ → .ρ] [.κ → .κ]))
  (define go
    (match-lambda
      ; E
      [(.↓ e ρ) (.↓ e (V-abs σ ρ))]
      [(.FC C V l) (.FC (go C) (go V) l)]
      [(.Mon C E l) (.Mon (go C) (go E) l)]
      [(.Assume V C) (.Assume (go V) (go C))]
      [(.blm l+ lo V C) (.blm l+ lo (go V) (go C))]
      [(? .V? V) (V-abs σ V)]
      ; k
      [(.if/κ t e) (.if/κ (go t) (go e))]
      [(.@/κ e* v* l) (.@/κ (map go e*) (map go v*) l)]
      [(.▹/κ (cons (? .E? C) #f) l) (.▹/κ (cons (go C) #f) l)]
      [(.▹/κ (cons #f (? .V? E)) l) (.▹/κ (cons #f (go E)) l)]
      [(.indy/κ Cs xs xs↓ d v? l)
       (.indy/κ (map go Cs) (map go xs) (map go xs↓)
                (match d
                  [(.↓ e ρ) (.↓ e (V-abs σ ρ))]
                  [_ #f]) v? l)]
      [(.λc/κ cs Cs d ρ v?) (.λc/κ cs (map go Cs) d (go ρ) v?)]
      [(.structc/κ t c ρ c↓) (.structc/κ t c (go ρ) (map go c↓))]
      [(.rt/κ (.λ↓ e ρ) x) (.rt/κ (.λ↓ e (go ρ)) x)]
      [(.blr/κ V) (.blr/κ (go V))]
      [(.recchk/κ c v) (.recchk/κ c (go v))]
      ; ρ
      [(? .ρ? ρ) (V-abs σ ρ)]
      [x x]))
  (.ς (go E) σ∅ (map go k)))