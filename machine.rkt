#lang racket
(require "syntax.rkt" "lang.rkt" "prim.rkt" "delta.rkt" "read.rkt" "show.rkt")
(provide
 #;(combine-out run ev)
 (contract-out
  [run (p? . -> . (set/c (cons/c σ? A?)))]
  [ev (any/c . -> . (set/c (cons/c σ? A?)))]))

(define (κ? x) ([or/c 'mt if/k? @/k? mon/k? mon*/k? lam/k?] x))
(struct if/k (e1 e2 k) #:transparent)
(struct @/k (l vs es k) #:transparent)
(struct mon/k (l+ l- lo c k) #:transparent)
(struct mon*/k (l+ l- lo Vs C Us k) #:transparent)
(struct lam/k (f xs σ k) #:transparent)

(struct ς (e σ k) #:transparent)

(define ς*? (nd/c ς?))

(define (run prog)
  (p? . -> . any/c)
  (match-define (p ms e†) prog)
  
  ; looks up value from module reference
  (define (ref-v m-name v-name)
    (l? l? . -> . v?)
    (hash-ref (m-defs (hash-ref ms m-name)) v-name (const (•))))
  
  ; looks up contract from module reference
  (define (ref-c m-name c-name)
    (l? l? . -> . c?)
    (hash-ref (m-decs (hash-ref ms m-name)) c-name))
  
  ; checks whether module exports given name
  (define (name-exported? f x)
    (l? l? . -> . boolean?)
    (hash-has-key? (m-decs (hash-ref ms f)) x))
  
  ; checks whether module is opaque
  (define (module-opaque? f)
    (match-let ([(m decs defs) (hash-ref ms f)])
      (for/or ([x (in-hash-keys decs)])
        (match? (hash-ref defs x (const (•))) (•)))))
  
  ; HACK. returns contracts that monitors value
  (define (v->c l v)
    (l? v? . -> . (or/c #f c?))
    (match-let ([(m decs defs) (hash-ref ms l)])
      (for/first ([(ki vi) (in-hash defs)] #:when (eq? #|FIXME hack|# v vi))
        (hash-ref decs ki (const #f)))))
  
  ; returns machine state for havoc-ing given value
  (define (havoc V σ k)
    (V? σ? . -> . ς?)
    (ς V σ [@/k '☠ `(,(close-v (ref-v '☠ 'havoc) ρ∅)) '() k]))
  
  (define (accel-@ l σ Vf Vx k k0)
    (l? σ? V? (listof V?) κ? κ? . -> . ς*?)
    
    ; checks whether recursive application is in tail-call position
    ; (ignoring lam/k frames)
    (define (tail? k kr)
      (or (eq? k kr) (match k
                       [(lam/k _ _ _ k1) (tail? k1 kr)]
                       [_ #f])))
    
    (define fc (match-let ([(val (close v _) _) Vf]) (v->c l v)))
    
    (match-let ([(val (close (f n e v?) ρ) Cs) Vf]
                [(lam/k Vg Vz σ1 _) k0])
      (cond
        [(E*⊑ Vx σ Vz σ1) ; recursive call by previous application subsuming it
         (if (tail? k k0) ∅ ; ignore unproductive tail calls
             (match fc
               [#f (ς ★ σ k)]
               [(func-c cx cy v?)
                ; only approximate by function's range if argument satisfies domain
                ; otherwise ⊤ is the only safe thing
                (if (for/and ([Vxi Vx] [cxi cx])
                      (equal? 'Proved (prove? σ Vxi (close cxi ρ∅))))
                    (match-let ([(cons σL L)
                                 (refine
                                  (σ+ σ)
                                  (close-c cy (ρ++ ρ∅ Vx (if v? (sub1 (length cx)) #f))))])
                      (ς L σL k))
                    (ς ★ σ k))]))]
        [else ; proceed with widened arguments
         (let-values
             ([(σn Wx)
               (match fc
                 [#f (widen* σ Vx)]
                 [(func-c cx cy v?)
                  (let-values
                      ([(σ2 Wx-rev)
                        (for/fold ([σ σ] [Wx empty]) ([Vxi Vx] [Vzi Vz] [cxi cx])
                          (if (or (E⊑ Vxi σ Vzi σ1) (V∈ Vxi σ1 Vzi)) (values σ (cons Vxi Wx))
                              (let ([Ci (close cxi ρ∅)])
                                (match (prove? σ Vxi Ci)
                                  ['Proved
                                   (match-let ([(cons σi Wi)
                                                (refine (widen (cons σ Vxi) 1) Ci)])
                                     (values σi (cons Wi Wx)))]
                                  [_ (match-let ([(cons σi Wi) (widen (cons σ Vxi))])
                                       (values σi (cons Wi Wx)))]))))])
                    (values σ2 (reverse Wx-rev)))])])
           (match v? ; proceed with approximate arguments
             [#f (if (= (length Vx) n)
                     (ς [close e (ρ++ ρ Wx)] σn [lam/k Vf Wx σn k])
                     (ς [bl l 'Δ "Expect ~a arguments, given ~a" n (length Vx)]
                        σn 'mt))]
             [#t (if (>= (length Vx) (sub1 n))
                     (ς [close e (ρ++ ρ Wx (sub1 n))] σn [lam/k Vf Wx σn k])
                     (ς [bl l 'Δ "Expect at least ~a arguments given ~a" (sub1 n) (length Vx)]
                        σn 'mt))]))])))
  
  ; steps an application state
  (define (step-@ l σ Vf Vx k)
    (l? σ? V? (listof V?) κ? . -> . ς*?)
    #;(printf "module ~a~n" l)
    #;(printf "Apply ~a~n" (show-E Vf) #;(map show-E Vx))
    (match Vf
      [(val u Cs)
       (match u
         [(? o? o) (match/nd (Δ l σ o Vx) [(cons σ1 A) (ς A σ1 k)])]
         [(close (f n e1 v?) ρf)
          (match (find-previous-call σ Vf Vx k)
            [#f (match v?
                  [#f (if (= (length Vx) n)
                          (ς [close-e e1 (ρ++ ρf Vx)] σ [lam/k Vf Vx σ k])
                          (ς [bl l 'Δ "Expect ~a arguments, given ~a" n (length Vx)]
                             σ 'mt))]
                  [#t (if (>= (length Vx) (sub1 n))
                          (ς [close-e e1 (ρ++ ρf Vx (sub1 n))] σ [lam/k Vf Vx σ k])
                          (ς [bl l 'Δ "Expect at least ~a arguments given ~a" (sub1 n) (length Vx)]
                             σ 'mt))])]
            [k0 (accel-@ l σ Vf Vx k k0)])]
         [(Arr l+ l- lo (close (func-c cx cy v?) ρc) Vg)
          (let ([V-len (length Vx)]
                [c-len (length cx)])
            (if (if v? (>= V-len c-len) (= V-len c-len))
                (ς Vg σ [mon*/k l- l+ lo '() (map (λ (c) (close-c c ρc)) cx) Vx
                                (mon/k1 l+ l- lo (close-c cy [ρ++ ρc Vx])
                                        (lam/k Vf Vx σ k))])
                (ς [bl l lo "Wrong arity"] σ 'mt)))]
         [_ (match/nd (Δ 'Δ σ (op 'proc?) `(,Vf))
              [(cons σ1 (val #t _))
               (match (arity-ok? (σ@* σ1 Vf) (length Vx))
                 [(or 'Y '?)
                  (match-let
                      ([havocs (for/set ([Vi Vx]) (havoc Vi σ k))]
                       [(cons σ2 V2) (for/fold ([σV (σ+ σ1)]) ([Ci (C-ranges Vx Cs)])
                                       (refine σV Ci))])
                    (set-add havocs (ς V2 σ2 k)))]
                 ['N (ς [bl l 'Δ (format "Wrong arity")] σ1 'mt)])]
              [(cons σ1 (val #f _)) (ς [bl l 'Δ "Apply non-function"] σ 'mt)])])]
      ; TODO: no need to remember whether σ[l] is function or not?
      [(? L? L) (step-@ l σ (σ@ σ L) Vx k)]))
  
  (define (step-fc lo C V σ k)
    (l? C? V? σ? κ? . -> . ς*?)
    (match (prove? σ V C)
      ['Proved (ς [val #t ∅] σ k)]
      ['Refuted (ς [val #f ∅] σ k)]
      [_
       (match-let ([(close c0 ρc) C])
         (match c0
           [(and-c c1 c2)
            (ς [FC lo (close-c c1 ρc) V] σ
               [if/k (FC lo (close-c c2 ρc) V) (val #f ∅) k])]
           [(or-c c1 c2)
            (ς [FC lo (close-c c1 ρc) V] σ
               [if/k (val #t ∅) (FC lo (close-c c2 ρc) V) k])]
           [(μ-c x c1)
            (match (prove? σ V C)
              ['Proved (ς (val #t ∅) σ k)]
              ['Refuted (ς (val #f ∅) σ k)]
              [_ {∪ (ς (val #f ∅) σ k)
                    (match/nd (refine (cons σ V) C)
                      [(cons σ1 V1) (ς [FC lo (close (subst/c c1 x c0) ρc) V1] σ1 k)])}])]
           [(struct-c t cs)
            ;; FIXME shameless code duplicate...
            (let ([n (length cs)])
              (match/nd (Δ 'Δ σ [struct-p t n] `[,V])
                [(cons σ1 [val #t _])
                 (let ([Vs (match V
                             [(val (Struct t Vs) _) Vs]
                             [(? L? l) (match (σ@ σ1 l)
                                         [(val (Struct t Vs) _) Vs]
                                         [_ (make-list n ★)])]
                             [_ (make-list n ★)])])
                   (ς [val #t ∅] σ1 [AND-FC lo cs ρc Vs k]))]
                [(cons σ1 [val #f _]) (ς [val #f ∅] σ1 k)]))]
           [(? v? v) (step-@ lo σ [close-v v ρc] (list V) k)]))]))
  
  (define (step-mon l+ l- lo C V σ k)
    (l? l? l? C? V? σ? κ? . -> . (nd/c ς?))
    (match-let ([(close c0 ρc) C])
      (match c0
        [(and-c c1 c2)
         (ς V σ [mon/k1 l+ l- lo (close-c c1 ρc)
                        [mon/k1 l+ l- lo (close-c c2 ρc) k]])]
        [(or-c c1 c2)
         (ς (FC lo [close-c c1 ρc] V) σ
            (if/k (Assume V [close-c c1 ρc])
                  (Mon l+ l- lo [close-c c2 ρc] V)
                  k))]
        [(? flat?)
         (match (prove? σ V C)
           ['Proved (ς V σ k)]
           ['Refuted (ς [bl l+ lo "Value ~a violates contract ~a" (show-E (σ@* σ V)) (show-C C)]
                        σ 'mt)]
           ['Neither (ς (FC lo C V) σ [if/k (Assume V C)
                                            (bl l+ lo "Value ~a violates contract ~a" (show-E (σ@* σ V)) (show-C C))
                                            k])])]
        
        [(μ-c x c1) (step-mon l+ l- lo [close-c (subst/c c1 x c0) ρc] V σ k)]
        [(struct-c t cs)
         (let ([n (length cs)])
           (match/nd (Δ 'Δ σ [struct-p t n] `[,V])
             [(cons σ1 [val #t _])
              (let ([Vs (match V
                          [(val (Struct t Vs) _) Vs]
                          [(? L? l) (match-let ([(val (Struct t Vs) _) (σ@ σ1 l)]) Vs)]
                          [_ (make-list n ★)])])
                (ς (val [struct-mk t n] ∅) σ1
                   [mon*/k l+ l- lo '()
                           (map (λ (ci) (close-c ci ρc)) cs) Vs k]))]
             [(cons σ1 [val #f _]) (ς [bl l+ lo "Expect a(n) ~a, given ~a" t (show-E (σ@* σ1 V))]
                                      σ1 'mt)]))]
        [(and [func-c cx cy v?] [? func-c? fc])
         (match/nd (Δ 'Δ σ [op 'proc?] `[,V])
           [(cons σ1 [val #t _])
            (let ([m (length cx)]
                  [ς-ok (ς (val [Arr l+ l- lo (close fc ρc) V] ∅) σ1 k)]
                  [ς-er (ς [bl l+ lo "Wrong arity"] σ1 'mt)])
              (cond
                [v? (match (min-arity-ok? [σ@* σ1 V] [sub1 m])
                      ['Y ς-ok]
                      ['N ς-er]
                      ['? {set ς-ok ς-er}])]
                [else (match (arity-ok? [σ@* σ1 V] m)
                        ['Y ς-ok]
                        ['N ς-er]
                        ['? {set ς-ok ς-er}])]))]
           [(cons σ1 [val #f _]) (ς [bl l+ lo "Apply non-function"] σ1 'mt)])])))
  
  (define (step-E E σ k)
    (E? σ? κ? . -> . (nd/c ς?))
    (match E
      [(close e ρ)
       (match e
         [(? x? x) (ς [ρ@ ρ x] σ k)]
         [(•) (match-let ([(cons σ1 l) (σ+ σ)]) (ς l σ1 k))]
         [(? v? v) (ς [close-v v ρ] σ k)]
         [(@ l ef exs)
          (ς [close-e ef ρ] σ [@/k l '() (for/list ([ei exs]) (close-e ei ρ)) k])]
         [(if/ e0 e1 e2) (ς [close-e e0 ρ] σ [if/k (close-e e1 ρ) (close-e e2 ρ) k])]
         [(amb es) (for/set ([ei es]) (ς (close-e ei ρ) σ k))]
         [(ref ctx ctx x) (ς [close-e (ref-v ctx x) ρ] σ k)]
         [(ref ctx src x) 
          (let* ([vx (ref-v src x)]
                 [cx (ref-c src x)]
                 [Cx (close-c cx ρ∅)])
            (match vx
              [(•) (match/nd (refine (σ+ σ) Cx)
                     [(cons σ1 l) (ς l σ1 [mon/k1 src ctx src Cx k])])]
              [_ (ς [close-v vx ρ∅] σ [mon/k1 src ctx src Cx k])]))])]
      
      [(? Blm? bl) (ς bl σ 'mt)]
      [(Mon l+ l- lo C E1) (ς E1 σ [mon/k1 l+ l- lo C k])]
      [(FC lo C V) (step-fc lo C V σ k)]
      [(Assume V C) (match/nd (refine [cons σ V] C)
                      [(cons σ1 V1) (ς V1 σ1 k)])]))
  
  (define (step-V V σ k)
    (V? σ? κ? . -> . (nd/c ς?))
    (match k
      [(if/k E1 E2 k1) 
       (match/nd (Δ 'Δ σ [op 'false?] (list V))
         [(cons σ1 [val #f _]) (ς E1 σ1 k1)]
         [(cons σ1 [val #t _]) (ς E2 σ1 k1)])]
      [(@/k l Vs [cons Ei Es] k1) (ς Ei σ [@/k l (cons V Vs) Es k1])]
      [(@/k l Vs '() k1) (match-let ([(cons Vf Vx) (reverse (cons V Vs))])
                           (step-@ l σ Vf Vx k1))]
      [(mon/k l+ l- lo C k1) (step-mon l+ l- lo C V σ k1)]
      [(mon*/k l+ l- lo Vs [cons Ci '()] [cons Vi Vs1] k1) 
       ; repeat last contract to handle var-args
       (ς Vi σ [mon/k1 l+ l- lo Ci (mon*/k l+ l- lo (cons V Vs) [cons Ci '()] Vs1 k1)])]
      [(mon*/k l+ l- lo Vs [cons Ci Cs] [cons Vi Vs1] k1) 
       (ς Vi σ [mon/k1 l+ l- lo Ci (mon*/k l+ l- lo (cons V Vs) Cs Vs1 k1)])]
      [(mon*/k l+ l- lo Vs _ '() k1) 
       (match-let ([(cons Vf Vx) (reverse (cons V Vs))])
         (step-@ l- σ Vf Vx k1))]
      [(lam/k _ _ _ k1) (ς V σ k1)]))
  
  (define (step s)
    (ς? . -> . ς*?)
    (match s
      [(ς [? V? V] σ k) (step-V V σ k)]
      [(ς E σ k) (step-E E σ k)]))
  
  
  (define (step* s)
    (ς? . -> . (set/c ς?))
    (let ([finals ∅])
      (let visit ([s s])
        (if (ς-final? s)
            ; omit blaming top, havoc, and opaque modules
            (unless (match? s (ς [Blm (or '† '☠ (? module-opaque?)) _ _] _ _))
              (set! finals (set-add finals s)))
            (non-det visit (step s))))
      finals))
  
  (for/set ([s (step* (inj e†))])
    (match-let ([(ς A σ _) s])
      (cons σ A))))

(define (ev p) (run (read-p p)))

(define (find-previous-call σ Vf Vx k)
  (σ? V? (listof V?) κ? . -> . (or/c #f lam/k?))
  (define go (curry find-previous-call σ Vf Vx))
  (match k
    [(lam/k (and Vg (val (close g _) _)) _ σ1 k1) (if (E⊑ Vf σ Vg σ1) k (go k1))]
    [(or (lam/k _ _ _ k1) (if/k _ _ k1) (@/k _ _ _ k1)
         (mon/k _ _ _ _ k1) (mon*/k _ _ _ _ _ _ k1)) (go k1)]
    ['mt #f]))

(define (V∈ V1 σ0 V0)
  (or (eq? V1 V0)
      (match V0
        [(val (Struct _ Vs) _) (for/or ([Vi Vs]) (V∈ V1 σ0 Vi))]
        [(? L? L) (V∈ V1 σ0 (σ@ σ0 L))]
        [_ #f])))

;; determine approximation between closures
(define (E⊑ E1 σ1 E2 σ2)
  (E? σ? E? σ? . -> . boolean?)
  (match* (E1 E2)
    [((close e1 ρ1) (close e2 ρ2)) (and (e⊑ e1 e2) (ρ⊑ ρ1 σ1 ρ2 σ2))]
    [((val U1 Cs) (val U2 Cs)) (U⊑ U1 σ1 U2 σ2)]
    [((Mon f g h C1 E1p) (Mon f g h C2 E2p))
     (and (C⊑ C1 σ1 C2 σ2) (E⊑ E1p σ1 E2p σ2))]
    [((FC l C1 V1) (FC l C2 V2)) (and (C⊑ C1 σ1 C2 σ2) (E⊑ V1 σ1 V2 σ2))]
    [((Assume V1 C1) (Assume V2 C2)) (and (C⊑ C1 σ1 C2 σ2) (E⊑ E1 σ1 E2 σ2))]
    [((and V (val U Cs1)) (val (•) Cs2))
     (for/and ([C Cs2]) (equal? 'Proved (prove? σ1 V C)))]
    [((val U1 _) (val U2 _)) (U⊑ U1 σ1 U2 σ2)]
    [((? L? L) _) (E⊑ (σ@ σ1 L) σ1 E2 σ2)]
    [(_ (? L? L)) (E⊑ E1 σ1 (σ@ σ2 L) σ2)]
    [(_ _) (equal? E1 E2)]))
(define (E*⊑ Es1 σ1 Es2 σ2)
  ((listof E?) σ? (listof E?) σ? . -> . boolean?)
  (for/and ([E1 Es1] [E2 Es2]) (E⊑ E1 σ1 E2 σ2)))

;; determine approximation between contracts
(define (C⊑ C1 σ1 C2 σ2)
  (match-let ([(close c1 ρ1) C1]
              [(close c2 ρ2) C2])
    (and (equal? c1 c2) (ρ⊑ ρ1 σ1 ρ2 σ2))))

;; determine approximation between environments
(define (ρ⊑ ρ1 σ1 ρ2 σ2)
  (match-let ([(ρ m1 len1) ρ1]
              [(ρ m2 len2) ρ2])
    (for/and ([sd (in-range 0 (min len1 len2))] #:when (ρ-has? ρ1 sd))
      (E⊑ (ρ@ ρ1 sd) σ1 (ρ@ ρ2 sd) σ2))))

;; determine approximation between prevalues
(define (U⊑ U1 σ1 U2 σ2)
  (match* (U1 U2)
    [((Struct t Vs1) (Struct t Vs2)) (E*⊑ Vs1 σ1 Vs2 σ2)]
    [((close f ρ1) (close f ρ2)) (ρ⊑ ρ1 σ1 ρ2 σ2)]
    [((Arr f g h C1 V1) (Arr f g h C2 V2)) (and (C⊑ C1 σ1 C2 σ2) (E⊑ V1 σ1 V2 σ2))]
    [(_ (•)) #t]
    [(_ _) (equal? U1 U2)]))

;; determine approximation between expressions
(define (e⊑ e1 e2) (or (•? e2) (equal? e1 e2)))

(define (widen σV [d 4])
  (((cons/c σ? V?)) (int?) . ->* . (cons/c σ? V?))
  (match-let ([(cons σ V) σV])
    (match V
      [(val U Cs)
       (match U
         [0 σV]
         [(? number?)
          (cons σ (val (•) (∪
                            Cs
                            (close (op (cond
                                         [(integer? U) 'int?]
                                         [(real? U) 'real?]
                                         [else 'num?]))
                                   ρ∅)
                            (if (real? U)
                                (close (op (if (positive? U) 'positive? 'negative?)) ρ∅)
                                ∅))))]
         [(? string?) (cons σ (val (•) (set-add Cs (close [op 'str?] ρ∅))))]
         [(Struct t Vs) (if (zero? d) (σ+ σ)
                            (let-values ([(σW Ws) (widen* σ Vs (sub1 d))])
                              (cons σW (val (Struct t Ws) Cs))))]
         [(close (f n _ v?) ρ) (cons σ (if (clo-circular? V)
                                           #;(val (close (f n (•) v?) ρ∅) Cs)
                                           (val
                                            (•)
                                            {set-add Cs (close (op 'proc?) ρ∅)
                                                     #;(close                                                      
                                                        (func-c (make-list n (f 1 (@ 'Δ (op 'false?) (list (x 0))) #f))
                                                                (op 'any)
                                                                v?)
                                                        ρ∅)})
                                           V))]
         [_ σV])]
      [_ σV])))
(define (widen* σ V* [d 4])
  (let-values ([(σW W*-rev)
                (for/fold ([σ σ] [W*-rev empty]) ([V V*])
                  (match-let ([(cons σi Wi) (widen (cons σ V) d)])
                    (values σi (cons Wi W*-rev))))])
    (values σW (reverse W*-rev))))

(define (AND-FC lo cs ρ Vs k)
  (l? (listof c?) ρ? (listof V?) κ? . -> . κ?)
  (match* (cs Vs)
    [('() '()) k]
    [([cons ci cs] [cons Vi Vs])
     (if/k (FC lo [close-c ci ρ] Vi) [val #f ∅] (AND-FC lo cs ρ Vs k))]))

;; collects range components of contracts
(define (C-ranges Vx Cs)
  ((listof V?) (set/c C?) . -> . (listof C?))
  (for/list ([Ci (in-set Cs)]
             #:when (match? Ci (close (? func-c?) _)))
    (match-let ([(close (func-c cx cy _) ρc) Ci])
      (close-c cy (ρ++ ρc Vx)))))

;; add monitoring frame and removes redundant ones below
(define (mon/k1 l+ l- lo Cn kn)
  (l? l? l? C? κ? . -> . κ?)
  (define (rm-mon k)
    (match k
      [(mon/k f g h Ci ki) (if (equal? 'Proved (C-prove? Cn Ci))
                               (rm-mon ki)
                               (mon/k f g h Ci (rm-mon ki)))]
      [_ k]))
  (mon/k l+ l- lo Cn (rm-mon kn)))

(define (inj e)
  (e? . -> . ς?)
  (ς [close e ρ∅] σ∅ 'mt))

(define (ς-final? s)
  (ς? . -> . boolean?)
  (match? s (ς [? A?] _ 'mt)))

;; pretty printing for debugging
(define/match (show-ς s)
  [((ς E σ k)) `(,(show-E E) ,σ ,(show-κ k))])
(define/match (show-κ k)
  [('mt) 'mt]
  [((if/k E1 E2 k)) `(IF/K ,(show-E E1) ,(show-E E2) ,(show-κ k))]
  [((@/k _ Vs Es k)) `(@/K ,(map show-E Vs) ,(map show-E Es) ,(show-κ k))]
  [((mon/k _ _ _ C k)) `(MON/K ,(show-C C) ,(show-κ k))]
  [((mon*/k _ _ _ _ Cs Us k)) `(MON*/k ,(map show-C Cs) ,(map show-E Us) ,(show-κ k))]
  [((lam/k f xs _ k)) `(LAM/K ,(show-E f) ,(map show-E xs) ,(show-κ k))])