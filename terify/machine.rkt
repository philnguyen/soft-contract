#lang typed/racket/base
(require
 racket/match racket/set racket/list racket/bool racket/function
 "utils.rkt" "lang.rkt" "closure.rkt" "delta.rkt" "provability.rkt" "show.rkt")
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
  (.structc/κ [t : Sym] [c : (Listof .e)] [ρ : .ρ] [c↓ : (Listof .V)]))
(define-type .κ* (Listof .κ))

; ctx in e's position for pending states
(struct: .ς ([e : .E] [s : .σ] [k : .κ*]) #:transparent)
(define-type .ς+ (Setof .ς))
(define-type .ς* (U .ς .ς+))

(: final? : .ς → Bool)
(define final?
  (match-λ? (.ς (? .blm?) _ _) (.ς (? .V?) _ (list))))

(: inj : .e → .ς)
(define (inj e)
  (.ς (.↓ e ρ∅) σ∅ empty))

(: print-ς : .ς → Void)
(define (print-ς ς)
  (define it (show-ς ς))
  (printf "E:~n ~a~n" (second (first it)))
  (printf "σ:~n")
  (for ([x (rest (second it))])
    (printf " ~a~n" x))
  (printf "k:~n")
  (for ([x (rest (third it))])
    (printf " ~a~n" x)))

(: ev : .p → (Option .Ans))
(define (ev p)
  (match-define (.p (and m* (.m* _ ms)) accs e) p)
  (define step (step-p m* accs))
  (define D 3)
  
  (: prob : Real → Boolean)
  (define (prob p) (<= (random) p))
  
  (: m-opaque? : Sym → Bool)
  (define (m-opaque? x) ; TODO: expensive?
    (match x
      ['† #t]
      ['☠ #t]
      [_
       (match-define (.m _ defs) (hash-ref ms x))
       (for/or ([d (in-hash-values defs)]
                #:when (.•ₗ? (car d)))
         #t)]))
  
  (: maybe-blame? : (U .κ* .ς) → Boolean)
  (define maybe-blame?
    (match-lambda
     [(list) #f]
     [(cons κ kᵣ)
      (match κ
        [(.if/κ (.blm l _ _ _) _) (not (m-opaque? l))]
        [(.if/κ _ (.blm l _ _ _)) (not (m-opaque? l))]
        [_ (maybe-blame? kᵣ)])]
     [(.ς _ _ k) (maybe-blame? k)]))
  
  (: on-new-state : (Setof .ς) .ς → (U (Setof .ς) .Ans))
  (define (on-new-state front ς)
    (match ς
      [(.ς (and blm (.blm l⁺ _ _ _)) σ _)
       (cond [(m-opaque? l⁺) front]
             [else (cons σ blm)])]
      [(.ς (? .V? V) σ k)
       (cond
        [(empty? k) front]
        [(maybe-blame? k)
         (match (ffw ς (set-count front) #|just a heuristic|#)
           [(? set? s) (set-union front s)]
           [(? cons? ans) ans])]
        [else (set-add front ς)])]
      [_ (set-add front ς)]))
  
  (: ffw : .ς Integer → (U (Setof .ς) .Ans))
  ;; Fast-forward
  (define (ffw ς n)
    (cond
     [(> n 0)
      (match (step ς)
        [(.ς (and blm (.blm l⁺ _ _ _)) σ _)
         (cond [(m-opaque? l⁺) ∅]
               [else (cons σ blm)])]
        [(? .ς? ς′)
         (cond
          [(final? ς′) ∅]
          [(maybe-blame? ς′) (ffw ς′ (- n 1))]
          [else {set ς′}])]
        [(? set? s)
         (for/fold ([acc : (U (Setof .ς) .Ans) ∅]) ([ς′ s])
           (cond ; FIXME duplicate code
            [(cons? acc) acc]
            [(final? ς′)
             (match ς′
               [(.ς (and blm (.blm (not (? m-opaque?)) _ _ _)) σ _)
                (cons σ blm)]
               [_ acc])]
            [(maybe-blame? ς′)
             (match (ffw ς′ (- n 1))
               [(? set? s) (set-union acc s)]
               [(? cons? ans) ans])]
            [else (set-add acc ς′)]))])]
     [else {set ς}]))
  
  (: batch-step : (Setof .ς) → (U (Setof .ς) .Ans))
  (define (batch-step front)
    (for/fold ([next : (U (Setof .ς) .Ans) ∅]) ([ς front])
      (cond
       [(cons? next) next] ; TODO: #:break, but TR doesn't like it
       [else
        (match (step ς)
          [(? .ς? ς′) (on-new-state next ς′)]
          [(? set? ςs)
           (for/fold ([next : (U (Setof .ς) .Ans) next]) ([ςᵢ ςs])
             (cond [(cons? next) next]
                   [else (on-new-state next ςᵢ)]))])])))
  
  (define stepᵢ 0)
  (: search : (Setof .ς) → (Option .Ans))
  (define (search front)
    #;(begin ; debug
      (printf "~a: ~a/~a~n"
              stepᵢ
              (for/sum ([ς front] #:when (maybe-blame? ς)) 1)
              (set-count front)))
    (cond
     [(set-empty? front) #f]
     [else
      (inc! stepᵢ)
      (define front′ (batch-step front))
      (cond
       [(set? front′) (search front′)]
       [else front′])]))
  
  ;; Interactive debugging
  #;(let ()
    (define l : (Listof Integer) '())
    (define stepᵢ 0)
    (let debug ([ς : .ς (inj e)])
      (match-define (.ς _ σ k) ς)
      (define b? (maybe-blame? k))
      (printf "~a: Stack: (~a) ~n" stepᵢ b?)
      (when b? (set! l (cons stepᵢ l)))
      (for ([κ k]) (printf " ~a~n" (show-κ σ κ)))
      (cond
       [(final? ς)
        (printf "Final:~n")
        (print-ς ς)
        (printf "forwardables: ~a" l)]
       [else
        (define next (step ς))
        (inc! stepᵢ)
        (cond
         [(set? next)
          (define n (set-count next))
          (define nextl : (Listof .ς) (set->list next))
          (printf "~a next states:~n" n)
          (for ([ςᵢ (in-list nextl)] [i n])
            (printf "~a:~n" i)
            (print-ς ςᵢ)
            (printf "~n"))
          (define next-choice : Integer
            (let prompt ()
              (printf "Explore [0 - ~a]: " (- n 1))
              (match (read)
                [(and (? exact-integer? k) (? (λ ([k : Integer]) (<= 0 k (- n 1))))) k]
                [_ (prompt)])))
          (debug (list-ref nextl next-choice))]
         [else (debug next)])]))
    (printf "Done, ~a steps taken~n" stepᵢ)
    (read)
    #f)
  
  (search (set (inj e))))

(define-syntax-rule (match/nd v [p e ...] ...) (match/nd: (.Ans → .ς) v [p e ...] ...))

(: step-p : .m* (Setof .st-ac) → (.ς → .ς*))
(define (step-p m* accs)  
  (match-define (.m* _ ms) m*)
  
  (: ref-e : Sym Sym → .e)
  (define (ref-e m x)
    (match-define (.m _ defs) (hash-ref ms m))
    (car (hash-ref defs x))) 
 
  (: ref-c : Sym Sym → .e)
  (define (ref-c m x)
    (match-define (.m _ decs) (hash-ref ms m))
    (match (cdr (hash-ref decs x))
      [(? .e? c) c]
      [_ (error (format "module ~a does not export ~a" m x))]))
  
  (: step-β : .λ↓ (Listof .V) Sym .σ .κ* → .ς)
  (define (step-β f Vx l σ k)
    #;(printf "Stepping ~a~n~n" (show-U σ f))
    (match-define (.λ↓ (.λ n e v?) ρ) f)
    (match v?
      [#f (if (= (length Vx) n)
              (.ς (.↓ e (ρ++ ρ Vx)) σ k)
              (.ς (.blm l 'Λ (Prim (length Vx)) (arity=/C n)) σ k))]
      [#t (if (>= (length Vx) (- n 1))
              (.ς (.↓ e (ρ++ ρ Vx (- n 1))) σ k)
              (.ς (.blm l 'Λ (Prim (length Vx)) (arity≥/C (- n 1))) σ k))]))
      
  (: step-@ : .V (Listof .V) Sym .σ .κ* → .ς*)
  (define (step-@ Vf V* l σ k)
    #;(printf "step-@:~n~a~n~a~n~n" (show-Ans σ Vf) (map (curry show-E σ) V*)) ;TODO reenable
    #;(printf "step-@:~nσ:~n~a~nf:~n~a~nx:~n~a~n~n" σ Vf V*)
    (match Vf
      [(.// U C*)
       (match U
         ;; Handle box operations specially
         [(.st-mk 'box 1)
          (match V*
            [(list _)
             #;(match-define (cons σ L) (σ+ σ))
             #;(.ς L (σ-set σ L (→V (.St 'box V*))) k)
             (error "TODO")]
            [_ (.ς (.blm l 'box (Prim (length V*)) (arity=/C 1)) σ k)])]
         [(.st-p 'box 1)
          (match V*
            [(list V)
             (match V
               [(.L i) (error "TODO")]
               [_ (.ς FF σ k)])]
            [_ (.ς (.blm l 'box? (Prim (length V*)) (arity=/C 1)) σ k)])]
         [(.st-ac 'box 1 0)
          (error "TODO")]
         [(.set-box!)
          (error "TODO")]
         [(? .o? o) (match/nd (dbg/off '@ (δ σ o V* l)) [(cons σa A) (.ς A σa k)])]
         [(? .λ↓? f) (step-β f V* l σ k)]
         [(.Ar (.// (.Λ/C C* D v?) _) Vg (and l^3 (list _ _ lo)))
          (define V# (length V*))
          (define C# (length C*))
          (define n (if v? (- C# 1) #f))
          (if (if v? (>= V# (- C# 1)) (= V# C#))
              (.ς Vg σ (cons (.indy/κ C* V* '() D n l^3) k))
              (.ς (.blm l lo (Prim (length V*))(if v? (arity≥/C (- C# 1)) (arity=/C C#))) σ k))]
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
               [(.// (? .Case? U) _)
                (match (.Case@ U V*)
                  [#f
                   (define-values (σ′ Lₐ) (σ+ σt))
                   (define Vf′ (→V (.Case+ U V* Lₐ)))
                   (.ς Lₐ (σ-set σ′ i Vf′) k)]
                  [(? .L? Lₐ)
                   (.ς Lₐ σt k)])]
               [_ (step-• L V* l σt k)])]
            [(cons σf (.// (.b #f) _)) (.ς (.blm l 'Λ Vf (arity-includes/C (length V*))) σf k)])]
         [(cons σf (.// (.b #f) _)) (.ς (.blm l 'Λ Vf PROC/C) σf k)])]))
  
  (: ς∪ : .ς* * → .ς+)
  (define (ς∪ . ςs)
    (match ςs
      [(list) ∅]
      [(list (? .ς? ς)) {set ς}]
      [(list (? set? s)) s]
      [_ (for/fold ([acc : .ς+ ∅]) ([ςᵢ ςs])
           (cond [(set? ςᵢ) (set-union acc ςᵢ)]
                 [else (set-add acc ςᵢ)]))]))
  
  (: step-• : .L (Listof .V) Sym .σ .κ* → .ς*)
  (define (step-• Lf V* l σ k)
    (ς∪ (step-havoc Lf V* σ k)
        (let ()
          (define-values (σ′ Lₐ) (σ+ σ))
          (define Vf (→V (.Case (hash-set ((inst hash (Listof .V) .L)) V* Lₐ))))
          (.ς Lₐ (σ-set σ′ Lf Vf) k))))
  
  (: step-havoc : .L (Listof .V) .σ .κ* → .ς*)
  (define (step-havoc Lf V* σ k)
    (match-define (.σ m l) σ)
    (match-define (.L α) Lf)
    (match V*
      [(list) ∅]
      [(list V)
       ;; Non-deterministically apply propriate operation then put back to unknown context
       (define x₀ (.x 0))
       (define ● (•!))
       (match V
         [(.// (.λ↓ (.λ n _ _) ρ) _)
          (define Vf (.λ↓ (.λ 1 (.@ ● (list (.@ x₀ (for/list ([_ n]) (•!)) '☠)) '☠) #f) ρ∅))
          (define σ′ (.σ (hash-set m α (→V Vf)) l))
          (step-β Vf V* '☠ σ′ k)]
         [(.// (.Ar (.// (.Λ/C cs _ _) _) _ _) _)
          (define n (length cs))
          (define Vf (.λ↓ (.λ 1 (.@ ● (list (.@ x₀ (for/list ([_ n]) (•!)) '☠)) '☠) #f) ρ∅))
          (define σ′ (.σ (hash-set m α (→V Vf)) l))
          (step-β Vf V* '☠ σ′ k)]
         [(.// (.St t Vs) _)
          (define n (length Vs))
          (for/fold ([ςs : (Setof .ς) ∅]) ([Vᵢ Vs] [i n])
            (define acc (.st-ac t n i))
            (define Vf (.λ↓ (.λ 1 (.@ ● (list (.@ acc (list x₀) '☠)) '☠) #f) ρ∅))
            (define σ′ (.σ (hash-set m α (→V Vf)) l))
            (set-add ςs (step-β Vf V* '☠ σ′ k)))]
         [(? .prim?) ∅]
         [_ ∅ #|TODO|#])]
      [_
       ;; Non-determistically havoc 1 arg
       (define ● (•!))
       (define n (length V*))
       (for/fold ([acc : (Setof .ς) ∅]) ([i n])
         (define Vf (.λ↓ (.λ n (.@ ● (list (.x i)) '☠) #f) ρ∅))
         (define σ′ (.σ (hash-set m α (→V Vf)) l))
         (set-add acc (step-β Vf V* '☠ σ′ k)))]))
  
  (: step-fc : .V .V Sym .σ .κ* → .ς*)
  (define (step-fc C V l σ k)
    (match (⊢ σ V C)
      ['Proved (.ς TT σ k)]
      ['Refuted (.ς FF σ k)]
      ['Neither
       (match C
         [(.// U D*)
          (match U
            [(and U (.μ/C x C′)) (step-fc (unroll/C U) V l σ k)]
            [(.St 'and/c (list C1 C2)) (and/ς (list (.FC C1 V l) (.FC C2 V l)) σ k)]
            [(.St 'or/c (list C1 C2)) (or/ς (list (.FC C1 V l) (.FC C2 V l)) σ k)]
            [(.St '¬/c (list C′)) (.ς (.FC C′ V l) σ (cons (.@/κ '() (list (Prim 'not)) l) k))]
            [(.St/C t C*)
             (match/nd (δ σ (.st-p t (length C*)) (list V) l)
               [(cons σt (.// (.b #t) _))
                (match-define (.// (.St t V*) _) (σ@ σt V))
                (and/ς (for/list ([Vi V*] [Ci C*]) (.FC Ci Vi l)) σ k)]
               [(cons σf (.// (.b #f) _)) (.ς FF σf k)])]
            [_ (step-@ C (list V) l σ k)])]
         [(.L _) (step-@ C (list V) l σ k)])]))
  
  (: step-▹ : .V .V Sym^3 .σ .κ* → .ς*)
  (define (step-▹ C V l^3 σ k)
    #;(printf "Mon:~nC:~a~nV:~a~nσ:~a~nk:~a~n~n" C V σ k)
    (match-define (list l+ l- lo) l^3)
    (match (⊢ σ V C) ; want a check here to reduce redundant cases for recursive contracts
      ['Proved (.ς V σ k)]
      ['Refuted (.ς (.blm l+ lo V C) σ k)]
      ['Neither
       (match C
         [(.L i) ; FIXME this is wrong, need to take care of higher-order contract
          (match-define (cons σt Vt) (refine σ V C))
          (match-define (cons σf Vf) (refine σ V (.¬/C C)))
          {set (.ς Vt σt k) (.ς Vf σf k)}]
         [(.// Uc C*)
          (match Uc
            [(and (.μ/C x C′) Uc) (step-▹ (unroll/C Uc) V l^3 σ k)]
            [(.St 'and/c (list Cₗ Cᵣ)) (.ς V σ (▹/κ1 Cₗ l^3 (▹/κ1 Cᵣ l^3 k)))]
            [(.St 'or/c (list Cₗ Cᵣ))
             (.ς (.FC Cₗ V lo) σ (cons (.if/κ (.Assume V Cₗ) (.Mon Cᵣ V l^3)) k))]
            [(.St '¬/c (list D))
             (.ς (.FC D V lo) σ (cons (.if/κ (.blm l+ lo V C) (.Assume V C)) k))]
            [(.St/C t C*)
             (define n (length C*))
             (match/nd (δ σ (.st-p t n) (list V) lo)
               [(cons σt (.// (.b #t) _))
                (match-define (.// (.St t V*) _) (dbg/off '▹ (σ@ σt V)))
                (.ς (→V (.st-mk t n)) σt
                    (cons (.@/κ (for/list ([C C*] [V V*]) (.Mon C V l^3)) '() lo) k))]
               [(cons σf (.// (.b #f) _)) (.ς (.blm l+ lo V (→V (.st-p t n))) σf k)])]
            [(and Uc (.Λ/C Cx* D v?))
             (match/nd (δ σ (.proc?) (list V) lo)
               [(cons σt (.// (.b #t) _))
                (match v?
                  [#f (match/nd (δ σt (.arity-includes?) (list V (Prim (length Cx*))) lo)
                        [(cons σt (.// (.b #t) _))
                         (.ς (→V (.Ar C V l^3)) σt k)]
                        [(cons σf (.// (.b #f) _))
                         (.ς (.blm l+ lo V (arity-includes/C (length Cx*))) σf k)])]
                  [#t (match/nd (δ σt (.arity≥?) (list V (Prim (- (length Cx*) 1))) lo)
                        [(cons σt (.// (.b #t) _))
                         (.ς (→V (.Ar C V l^3)) σt k)]
                        [(cons σf (.// (.b #f) _))
                         (.ς (.blm l+ lo V (arity≥/C (- (length Cx*) 1))) σf k)])])]
               [(cons σf (.// (.b #f) _)) (.ς (.blm l+ lo V PROC/C) σf k)])]
            [_ (.ς (.FC C V lo) σ (cons (.if/κ (.Assume V C) (.blm l+ lo V C)) k))])])]))
  
  (: step-E : .E .σ .κ* → .ς*)
  (define (step-E E σ k)
    #;(printf "E: ~a~n~n" E)
    (match E
      [(.↓ e ρ)
       (match e
         [(.•ₗ n)
          (match-define (.σ m l) σ)
          (.ς (.L n) (.σ (hash-update m n identity (λ () ♦)) l) k)]
         [(? .v? v) (.ς (close v ρ) σ k)]
         [(.x sd) (.ς (ρ@ ρ sd) σ k)]
         [(.x/c x) (.ς (ρ@ ρ x) σ k)]
         [(.ref name ctx ctx) (.ς (.↓ (ref-e ctx name) ρ∅) σ k)]
         [(.ref name in ctx)
          (.ς (.↓ (ref-c in name) ρ∅) σ
              (cons (.▹/κ  (cons #f (.↓ (ref-e in name) ρ∅)) (list in ctx in)) k))]
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
      [(.Assume V C)
       (match-define (cons σ′ V′) (refine σ V C))
       (.ς V′ σ′ k)]))
  
  (: step-V : .V .σ .κ .κ* → .ς*)
  (define (step-V V σ κ k)
    (match κ
      [(.if/κ E1 E2)
       (match/nd (δ σ .false/c (list V) 'Λ)
         [(cons σt (.// (.b #f) _)) (.ς E1 σt k)]
         [(cons σf (.// (.b #t) _)) (.ς E2 σf k)])]
      
      [(.@/κ (cons E1 Er) V* l) (.ς E1 σ (cons (.@/κ Er (cons V V*) l) k))]
      [(.@/κ '() V* l)
       (match-define (cons Vf Vx*) (reverse (cons V V*)))
       (step-@ Vf Vx* l σ k)]
      
      [(.▹/κ (cons #f (? .E? E)) l^3)
       (.ς E σ (▹/κ1 V l^3 k))]
      [(.▹/κ (cons (? .V? C) #f) l^3) (step-▹ C V l^3 σ k)]
      
      
      ;; indy
      [(.indy/κ (list Ci) (cons Vi Vr) Vs↓ D n l^3) ; repeat last contract, handling var-args
       (step-▹ Ci Vi (¬l l^3) σ (cons (.indy/κ (list Ci) Vr (cons V Vs↓) D n l^3) k))]
      [(.indy/κ (cons Ci Cr) (cons Vi Vr) Vs↓ D n l^3)
       (step-▹ Ci Vi (¬l l^3) σ (cons (.indy/κ Cr Vr (cons V Vs↓) D n l^3) k))]
      [(.indy/κ _ '() Vs↓ (.↓ d ρ) n l^3) ; evaluate range contract
       (match-define (and V* (cons Vf Vx*)) (reverse (cons V Vs↓)))
       (.ς (.↓ d (ρ++ ρ Vx* n)) σ (cons (.indy/κ '() '() V* #f n l^3) k))]
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
    [(cons E Er)
     (.ς E σ (foldr (λ ([Ei : .E] [k : .κ*])
                      (cons (.if/κ Ei FF) k))
                    k Er))]))

(: or/ς : (Listof .E) .σ .κ* → .ς)
(define (or/ς E* σ k)
  (match E*
    ['() (.ς FF σ k)]
    [(list E) (.ς E σ k)]
    [(cons E Er)
     (.ς E σ (foldr (λ ([Ei : .E] [k : .κ*])
                      (cons (.if/κ TT Ei) k))
                    k Er))]))

(: ▹/κ1 : .V Sym^3 .κ* → .κ*)
(define (▹/κ1 C l^3 k)
  (match C
    [(.// (.λ↓ (.λ 1 (.b #t) _) _) _) k]
    [(.// (? .Λ/C?) _) (cons (.▹/κ (cons C #f) l^3) k)]
    [_ (cons (.▹/κ (cons C #f) l^3)
             (let trim : .κ* ([k : .κ* k])
               (match k
                 [(cons (and κ (.▹/κ (cons (? .V? D) #f) _)) kr)
                  (match (C⇒C C D)
                    ['Proved (trim kr)]
                    [_ (cons κ (trim kr))])]
                 [_ k])))]))

;;;;; small programs for testing
(define f
  (read-p
   `((module f
       (provide [f (int? . -> . int?)])
       (define (f n)
         (if (= n 0) 1 (* n (f (- n 1))))))
     (require f)
     (f 100))))

;; for debugging
(define (e x) (ev (read-p x)))

(: show-k : .σ .κ* → (Listof Any))
(define (show-k σ k) (for/list ([κ k]) (show-κ σ κ)))

(: show-κ : .σ .κ → Any)
(define (show-κ σ κ)
  (define E (curry show-E σ))
  (match κ
    [(.if/κ t e) `(if ● ,(E t) ,(E e))]
    [(.@/κ e* v* _) `(@ ,@(reverse (map E v*)) ● ,@(map E e*))]
    [(.▹/κ (cons #f (? .E? e)) l³) `(● ▹ ,(E e) ,l³)]
    [(.▹/κ (cons (? .E? C) #f) l³) `(,(E C) ,l³ ▹ ●)]
    [(.indy/κ Cs xs xs↓ d _ _) `(indy ,(map E Cs) ,(map E xs) ,(map E xs↓)
                                      ,(match d [#f '_] [(? .E? d) (E d)]))]
    [(.μc/κ x) `(μ/c ,x ●)]
    [(.λc/κ cs Cs d ρ _)
     `(λ/c (,@(reverse (map E Cs)) ,@(map (curry show-e σ) cs)) ,(show-e σ d))]
    [(.structc/κ t c _ c↓)
     `(struct/c ,t (,@(reverse (map E c↓)) ,(map (curry show-e σ) c)))]))

(: show-ς : .ς → (List (Listof Any) (Listof Any) (Listof Any)))
(define show-ς
  (match-lambda
    [(.ς E σ k) `((E: ,(show-E σ E))
                  (σ: ,@(show-σ σ))
                  (k: ,@(show-k σ k)))]))
