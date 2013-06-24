#lang racket
(require "syntax.rkt" "lang.rkt" "prim.rkt" "delta.rkt" "read.rkt")
(provide run ev)

(define (κ? x) ([or/c 'mt if/k? @/k? mon/k? vmon/k?] x))
(struct if/k (e1 e2 k) #:transparent)
(struct @/k (l vs es k) #:transparent)
(struct mon/k (l+ l- lo c k) #:transparent)
(struct vmon/k (l+ l- lo Vs C Us k) #:transparent)

(struct ς (e σ k) #:transparent)

(define ς+? (or/c ς? (set/c ς?)))
(define MemoRec? (listof [list/c (listof V?) σ? κ?]))
(define Memo? (hash/c [or/c (cons/c l? V?) C?] MemoRec?))

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
  (define (havoc V σ)
    (V? σ? . -> . ς?)
    (ς V σ [@/k '☠ `(,(close-v (ref-v '☠ 'havoc) ρ∅)) '() 'mt]))
  
  ; steps an application state
  (define (step-@ l σ1 Vf Vx k)
    (l? σ? V? (listof V?) κ? . -> . ς+?)
    (match Vf
      [(val u Cs)
       (match u
         [(? o? o) (match/nd (Δ l σ1 o Vx) [(cons σ2 A) (ς A σ2 k)])]
         [(close (f n e1 #f) ρf) (if (= n (length Vx))
                                     (ς [close e1 (ρ++ ρf Vx)] σ1 k)
                                     (ς [Blm l 'Δ] σ1 'mt))]
         [(close (f n e1 #t) ρf) (if (<= [sub1 n] (length Vx))
                                     (ς [close e1 (bind-vars ρf Vx [sub1 n])] σ1 k)
                                     (ς [Blm l 'Δ] σ1 'mt))]
         [(Arr l+ l- lo [close (func-c cx cy #f) ρc] Vg)
          (if (= (length cx) (length Vx))
              (ς Vg σ1 [vmon/k l- l+ lo '() (map (λ (ci) (close-c ci ρc)) cx) Vx
                               ; FIXME: use indie!!!
                               [mon/k1 l+ l- lo (close-c cy [ρ++ ρc Vx]) k]])
              (ς (Blm l lo) σ1 'mt))]
         [(Arr l+ l- lo [close (func-c cx cy #t) ρc] Vg)
          (if (<= (length cx) (length Vx))
              (ς Vg σ1 [vmon/k l- l+ lo '() (map (λ (ci) (close-c ci ρc)) cx) Vx
                               ; FIXME: use indie!!!
                               [mon/k1 l+ l- lo (close-c cy [ρ++ ρc Vx]) k]])
              (ς (Blm l lo) σ1 'mt))]
         [_ (match/nd (Δ 'Δ σ1 [op 'proc?] `[,Vf])
              [(cons σ2 [val #t _])
               (match (arity-ok? [σ@* σ2 Vf] (length Vx))
                 [(or 'Y '?)
                  (∪ (for/set ([Vi Vx]) (havoc Vi σ2))
                     (match/nd (for/fold ([σV (σ+ σ2)]) ([C (C-ranges Vx Cs)])
                                 (non-det (λ (σV) (refine σV C)) σV))
                       [(cons σ3 V3) (ς V3 σ3 k)]))]
                 ['N (ς [Blm l 'Δ] σ2 'mt)])]
              [(cons σ2 [val #f _]) (ς [Blm l 'Δ] σ1 'mt)])])]
      ; TODO: no need to remember whether σ[l] is function or not?
      [(? L? lab) (step-@ l σ1 [σ@ σ1 lab] Vx k)]))
  
  (define (maybe-@ m l σ1 Vf Vx k)
    (Memo? l? σ? V? (listof V?) κ? . -> . (nd/c ς?))
    #;(printf "ABOUT to apply:~n~nf: ~a~n~nxs: ~a~n~nk: ~n~n~n" Vf Vx k)
    (or (for/or ([r (hash-ref m [cons l Vf] (const empty))])
          (match-let ([(list Vz σi ki) r])
            (cond
              [(not (κ-prefix? ki k)) #f]
              [(equal? k ki)
               (cond
                 [(and (Es/σ-equal? Vx σ1 Vz σi) (κ/σ-equal? ki σi k σ1))
                  #;(printf "IGNORE repeated state with garbage~n")
                  ∅] ; old state with more garbage
                 [(ormap opaque? Vx)
                  #;(printf "WIDEN arguments for recursive tail call~nf: ~a~n~nxs: ~a~n~nxs′: ~a~n~n~n"
                            Vf Vx (map V-approx Vx))
                  (step-@ l σ1 Vf (map V-approx Vx) k)]
                 [else #f])]
              [(Es/σ-equal? Vx σ1 Vz σi)
               (match Vf
                 [(val (close (? f? f) _) _)
                  (match (v->c l f)
                    [#f #f]
                    [c
                     #;(printf "APPROX by contract~n")
                     (match/nd (for/fold ([σV (σ+ σ1)]) ([C (C-ranges Vx {set (close c ρ∅)})])
                                    (non-det (λ (σV) (refine σV C)) σV))
                       [(cons σa Va) (ς Va σa k)])])]
                 #;[(val [? o? o] _)
                    (printf "APPROX by prim op's range~n")
                    (ς [o-range o] σ1 k)]
                 [_ #f])]
              [else #f])))
        (step-@ l σ1 Vf Vx k)))
  
  (define (step-fmon m lo C0 V0 σ0 k)
    (Memo? l? C? V? σ? κ? . -> . (nd/c ς?))
    (match (prove? σ0 V0 C0)
      ['Proved (ς [val #t ∅] σ0 k)]
      ['Refuted (ς [val #f ∅] σ0 k)]
      [_
       (match-let ([(close c0 ρc) C0])
         (match c0
           [(and-c c1 c2)
            (ς [Fmon lo (close-c c1 ρc) V0] σ0
               [if/k (Fmon lo (close-c c2 ρc) V0) (val #f ∅) k])]
           [(or-c c1 c2)
            (ς [Fmon lo (close-c c1 ρc) V0] σ0
               [if/k (val #t ∅) (Fmon lo (close-c c2 ρc) V0) k])]
           [(μ-c x c1)
            (match (prove? σ0 V0 C0)
              ['Proved (ς (val #t ∅) σ0 k)]
              ['Refuted (ς (val #f ∅) σ0 k)]
              [_ {∪ (ς (val #f ∅) σ0 k)
                    (match/nd (refine (cons σ0 V0) C0)
                      [(cons σ1 V1) (ς [Fmon lo (close (subst/c c1 x c0) ρc) V1] σ1 k)])}])]
           [(struct-c t cs)
            ;; FIXME shameless code duplicate...
            (let ([n (length cs)])
              (match/nd (Δ 'Δ σ0 [struct-p t n] `[,V0])
                [(cons σ1 [val #t _])
                 (let ([Vs (match V0
                             [(val (Struct t Vs) _) Vs]
                             [(? L? l) (match (σ@ σ1 l)
                                         [(val (Struct t Vs) _) Vs]
                                         [_ (make-list n ★)])]
                             [_ (make-list n ★)])])
                   (ς [val #t ∅] σ1 [AND-FMON lo cs ρc Vs k]))]
                [(cons σ1 [val #f _]) (ς [val #f ∅] σ1 k)]))]
           [(? v? v) (maybe-@ m lo σ0 [close-v v ρc] (list V0) k)]))]))
  
  (define (step-mon l+ l- lo C V σ k)
    (l? l? l? C? V? σ? κ? . -> . (nd/c ς?))
    (match-let ([(close c0 ρc) C])
      (match c0
        [(and-c c1 c2)
         (ς V σ [mon/k1 l+ l- lo (close-c c1 ρc)
                        [mon/k1 l+ l- lo (close-c c2 ρc) k]])]
        [(or-c c1 c2)
         (ς (Fmon lo [close-c c1 ρc] V) σ
            (if/k (Assume V [close-c c1 ρc])
                  (Mon l+ l- lo [close-c c2 ρc] V)
                  k))]
        [(? flat?)
         (match (prove? σ V C)
           ['Proved (ς V σ k)]
           ['Refuted (ς [Blm l+ lo] σ 'mt)]
           ['Neither (ς (Fmon lo C V) σ [if/k (Assume V C) (Blm l+ lo) k])])]
        
        [(μ-c x c1) (step-mon l+ l- lo [close-c (subst/c c1 x c0) ρc] V σ k)]
        [(struct-c t cs)
         (let ([n (length cs)])
           (match/nd (Δ 'Δ σ [struct-p t n] `[,V])
             [(cons σ1 [val #t _])
              (let ([Vs (match V
                          [(Struct t Vs) Vs]
                          [(? L? l) (match-let ([(Struct t Vs) (σ@ σ1 l)]) Vs)]
                          [_ (make-list n ★)])])
                (ς (val [struct-mk t n] ∅) σ1
                   [vmon/k l+ l- lo '()
                           (map (λ (ci) (close-c ci ρc)) cs) Vs k]))]
             [(cons σ1 [val #f _]) (ς [Blm l+ lo] σ1 'mt)]))]
        [(and [func-c cx cy v?] [? func-c? fc])
         (match/nd (Δ 'Δ σ [op 'proc?] `[,V])
           [(cons σ1 [val #t _])
            (let ([m (length cx)]
                  [ς-ok (ς (val [Arr l+ l- lo (close fc ρc) V] ∅) σ1 k)]
                  [ς-er (ς [Blm l+ lo] σ1 'mt)])
              (cond
                [v? (match (min-arity-ok? [σ@* σ1 V] [sub1 m])
                      ['Y ς-ok]
                      ['N ς-er]
                      ['? {set ς-ok ς-er}])]
                [else (match (arity-ok? [σ@* σ1 V] m)
                        ['Y ς-ok]
                        ['N ς-er]
                        ['? {set ς-ok ς-er}])]))]
           [(cons σ1 [val #f _]) (ς [Blm l+ lo] σ1 'mt)]
           )])))
  
  (define (step-E m E σ k)
    (Memo? E? σ? κ? . -> . (nd/c ς?))
    (match E
      [(close e0 ρ)
       (match e0
         [(? x? x) (ς [ρ@ ρ x] σ k)]
         [(•) (match-let ([(cons σ1 l) (σ+ σ)]) (ς l σ1 k))]
         [(? v? v) (ς [close-v v ρ] σ k)]
         [(@ l ef exs)
          (ς [close-e ef ρ] σ [@/k l '() (for/list ([ei exs]) (close-e ei ρ)) k])]
         [(if/ e e1 e2) (ς [close-e e ρ] σ [if/k (close-e e1 ρ) (close-e e2 ρ) k])]
         [(amb es) (for/set ([ei es]) (ς (close-e ei ρ) σ k))]
         [(ref ctx ctx x) (ς [close-e (ref-v ctx x) ρ] σ k)]
         [(ref ctx src x) 
          (let* ([vx (ref-v src x)]
                 [cx (ref-c src x)]
                 [Cx (close-c cx ρ∅)])
            (match vx
              [(? •? v•) (match/nd (refine (σ+ σ) Cx)
                           [(cons σ1 l) (ς l σ1 [mon/k1 src ctx src Cx k])])]
              [_ (ς [close-v vx ρ∅] σ [mon/k1 src ctx src Cx k])]))])]
      
      [(and bl (Blm l+ lo)) (ς bl σ 'mt)]
      [(Mon l+ l- lo C0 E0) (ς E0 σ [mon/k1 l+ l- lo C0 k])]
      [(Fmon lo C0 V0) (step-fmon m lo C0 V0 σ k)]
      [(Assume V0 C0) (match/nd (refine [cons σ V0] C0)
                        [(cons σ1 V1) (ς V1 σ1 k)])]))
  
  (define (step-V m V0 σ k)
    (Memo? V? σ? κ? . -> . (nd/c ς?))
    (match k
      [(if/k E1 E2 k1) 
       (match/nd (Δ 'Δ σ [op 'false?] (list V0))
         [(cons σ1 [val #f _]) (ς E1 σ1 k1)]
         [(cons σ1 [val #t _]) (ς E2 σ1 k1)])]
      [(@/k l Vs [cons Ei Es] k1) (ς Ei σ [@/k l (cons V0 Vs) Es k1])]
      [(@/k l Vs '() k1) (match-let ([(cons Vf Vx) (reverse (cons V0 Vs))])
                           (maybe-@ m l σ Vf Vx k1))]
      [(mon/k l+ l- lo C k1) (step-mon l+ l- lo C V0 σ k1)]
      [(vmon/k l+ l- lo Vs [cons Ci '()] [cons Vi Vs1] k) 
       ; repeat last contract to handle var-args
       (ς Vi σ [mon/k1 l+ l- lo Ci [vmon/k l+ l- lo (cons V0 Vs) [cons Ci '()] Vs1 k]])]
      [(vmon/k l+ l- lo Vs [cons Ci Cs] [cons Vi Vs1] k) 
       (ς Vi σ [mon/k1 l+ l- lo Ci [vmon/k l+ l- lo (cons V0 Vs) Cs Vs1 k]])]
      [(vmon/k l+ l- lo Vs _ '() k) 
       (match-let ([(cons Vf Vx) (reverse (cons V0 Vs))])
         (maybe-@ m l- σ Vf Vx k))]))
  
  (define (step s m)
    (ς? Memo? . -> . (nd/c ς?))
    (match s
      [(ς [? V? V] σ k) (step-V m V σ k)]
      [(ς E σ k) (step-E m E σ k)]))
  
  
  (define (step* s)
    (ς? . -> . (set/c ς?))
    #;(define: seen : [Setof ς] ∅)
    (define finals ∅)
    
    (let visit ([s s] [m #hash()])
      (if (ς-final? s)
          (begin
            #;(printf "FINAL:~n~a~n~n" (show-ς s))
            ; omit blaming top, havoc, and opaque modules
            (unless (match? s (ς [Blm (or '† '☠ (? module-opaque?)) _] _ _))
              (set! finals (set-add finals s))))
          (begin
            #;(printf "NON-FINAL:~n~a~n~n" (show-ς s))
            #;(set! seen (set-add seen s))
            (let ([m1 (match s
                        [(ς [? V? Vn] σi [@/k l Vs '() ki])
                         (match-let ([(cons Vf Vx) (reverse (cons Vn Vs))])
                           (hash-update m [cons l Vf]
                                        (λ (r) (cons [list Vx σi ki] r))
                                        (const empty)))]
                        [_ m])])
              (match (step s m)
                [(? ς? s1) (visit s1 m1)]
                [(? set? ss) (for ([si (in-set ss)]) (visit si m1))])))))
    #;(printf "#states: ~a~n" (+ (set-count seen) (set-count finals)))
    finals)
  
  (for/set ([s (step* (inj e†))])
    (match-let ([(ς A0 σ _) s])
      (A→EA σ A0))))

(define (ev p) (run (read p)))

(define (ρ/σ-equal? ρ1 σ1 ρ2 σ2) ; they close the same expression, so must have same dom
  (ρ? σ? ρ? σ? . -> . boolean?)
  (match-let ([(ρ m1 len1) ρ1]
              [(ρ m2 len2) ρ2])
    (for/and ([sd (in-range 0 (min len1 len2))] #:when (ρ-has? ρ1 sd))
      (E/σ-equal? (ρ@ ρ1 sd) σ1 (ρ@ ρ2 sd) σ2))))

(define (E/σ-equal? E1 σ1 E2 σ2)
  (E? σ? E? σ? . -> . boolean?)
  (match* (E1 E2)
    [([close e ρ1] [close e ρ2]) (ρ/σ-equal? ρ1 σ1 ρ2 σ2)]
    [([val u1 Cs] [val u2 Cs])
     (match* (u1 u2)
       [([close f ρ1] [close f ρ2]) (ρ/σ-equal? ρ1 σ1 ρ2 σ2)]
       [([Arr f g h C V1] [Arr f g h C V2]) (E/σ-equal? V1 σ1 V2 σ2)]
       [([Struct t Vs1] [Struct t Vs2]) (for/and ([V1 Vs1] [V2 Vs2])
                                          (E/σ-equal? V1 σ1 V2 σ2))]
       [(_ _) (equal? u1 u2)])]
    [([Mon f g h C E1′] [Mon f g h C E2′]) (E/σ-equal? E1′ σ1 E2′ σ2)]
    [([Fmon l C V1] [Fmon l C V2]) (E/σ-equal? V1 σ1 V2 σ2)]
    [([Assume V1 C] [Assume V2 C]) (E/σ-equal? V1 σ1 V2 σ2)]
    [([? L? l1] E2′) (E/σ-equal? [σ@ σ1 l1] σ1 E2′ σ2)]
    [(E1 [? L? l2]) (E/σ-equal? E1 σ1 [σ@ σ2 l2] σ2)]
    [(_ _) (equal? E1 E2)]))

(define (Es/σ-equal? Es1 σ1 Es2 σ2)
  ((listof E?) σ? (listof E?) σ? . -> . boolean?)
  (for/and ([E1 Es1] [E2 Es2])
    (E/σ-equal? E1 σ1 E2 σ2)))

(define (κ/σ-equal? k1 σ1 k2 σ2)
  (κ? σ? κ? σ? . -> . boolean?)
  (match* (k1 k2)
    [('mt 'mt) #t]
    [([if/k E1a E1b k1′] [if/k E2a E2b k2′])
     (and [E/σ-equal? E1a σ1 E2a σ2]
          [E/σ-equal? E1b σ1 E2b σ2]
          [κ/σ-equal? k1′ σ1 k2′ σ2])]
    [([@/k _ vs1 es1 k1′] [@/k _ vs2 es2 k2′])
     (and [Es/σ-equal? vs1 σ1 vs2 σ2]
          [Es/σ-equal? es1 σ1 es2 σ2]
          [κ/σ-equal? k1′ σ1 k2′ σ2])]
    [([mon/k _ _ _ C k1′] [mon/k _ _ _ C k2′]) (κ/σ-equal? k1′ σ1 k2′ σ2)]
    [([vmon/k _ _ _ Vs1 Cs Us1 k1′] [vmon/k _ _ _ Vs2 Cs Us2 k2′])
     (and [Es/σ-equal? Vs1 σ1 Vs2 σ2]
          [Es/σ-equal? Us1 σ1 Us2 σ2]
          [κ/σ-equal? k1′ σ1 k2′ σ2])]
    [(_ _) #f]))

;; checks whether the first kontinuation is a prefix of the second one
(define (κ-prefix? k1 k2)
  (κ? κ? . -> . boolean?)
  (or (equal? k1 k2)
      (match k2
        ['mt #f]
        [(or [if/k _ _ k] [@/k _ _ _ k] [mon/k _ _ _ _ k] [vmon/k _ _ _ _ _ _ k])
         (κ-prefix? k1 k)])))

(define (ρ-approx ρ1)
  (ρ? . -> . ρ?)
  (match-let ([(ρ m len) ρ1])
    (ρ (for/hash ([(k v) (in-hash m)])
         (values k [V-approx v]))
       len)))

(define (V-approx V [d 7])
  ((V?) (int?) . ->* . V?)
  (match V
    [(val u Cs)
     (match u
       [(? integer?) (val (•) (set-add Cs (close [op 'int?] ρ∅)))]
       [(? real?) (val (•) (set-add Cs (close [op 'real?] ρ∅)))]
       [(? number?) (val (•) (set-add Cs (close [op 'num?] ρ∅)))]
       [(? string?) (val (•) (set-add Cs (close [op 'str?] ρ∅)))]
       [(Struct t Vs) (if (zero? d) ★
                          (val (Struct t (for/list ([Vi Vs])
                                           (V-approx Vi (sub1 d))))
                               Cs))]
       [_ V])]
    [_ V]))

(define (AND-FMON lo cs ρ Vs k)
  (l? (listof c?) ρ? (listof V?) κ? . -> . κ?)
  (match* (cs Vs)
    [('() '()) k]
    [([cons ci cs] [cons Vi Vs])
     (let ([k1 (AND-FMON lo cs ρ Vs k)])
       (if/k (Fmon lo [close-c ci ρ] Vi) [val #f ∅] k1))]))

;; collects range components of contracts
(define (C-ranges Vx Cs)
  ((listof V?) (set/c C?) . -> . (listof C?))
  (for/list ([Ci (in-set Cs)]
             #:when (match? Ci (close (? func-c?) _)))
    (match-let ([(close (func-c cx cy _) ρc) Ci])
      (close-c cy (ρ++ ρc Vx)))))

;; bind arguments for var-args function
(define MT (val [Struct 'empty '()] ∅))
(define (bind-vars ρ1 Vx n)
  (ρ? (listof V?) int? . -> . ρ?)
  (cond
    [(zero? n) (ρ+ ρ1 [foldr (λ (X Xs) (val [Struct 'cons (list X Xs)] ∅)) MT Vx])]
    [else (bind-vars [ρ+ ρ1 (car Vx)] [cdr Vx] [sub1 n])]))

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

(define (close-e e ρ)
  (e? ρ? . -> . E?)
  (match e
    [(•) (close e ρ∅)]
    [(? v? v) (close-v v ρ)]
    [_ (close e (ρ-restrict ρ (FV e)))]))

(define (close-v v ρ)
  (v? ρ? . -> . V?)
  (match v
    [(? b? b) (val b ∅)]
    [(? f? lam) (val [close lam (ρ-restrict ρ (FV lam))] ∅)]))

(define (close-c c ρ)
  (c? ρ? . -> . C?)
  (close c [ρ-restrict ρ (FV-c c)]))

(define (inj e)
  (e? . -> . ς?)
  (ς [close e ρ∅] σ∅ 'mt))

(define (ς-final? s)
  (ς? . -> . boolean?)
  (match? s (ς [? A?] _ 'mt)))

;; readable evaluation answer
(define (A→EA σ a)
  (σ? A? . -> . any/c)
  (match a
    [(? L? l) (A→EA σ [σ@ σ l])]
    [(Blm f+ fo) `(blame ,f+ ,fo)]
    [(val w cs)
     (match w
       [(and b (or [? number?] [? boolean?] [? string?] [? symbol?])) b]
       [(or [? Arr?] [? o?] [close [? f?] _]) 'function]
       [(Struct t Vs) `(,t ,@ (map (curry A→EA σ) Vs))]
       [(•) (match (map C→EC (set->list cs))
              ['() '•]
              [cs (cons '• cs)])])]))

(define/match (C→EC C)
  ;((or/c C? c?) . -> . any/c)
  [((close c ρ)) (C→EC c)]
  [((and-c c1 c2)) `(,[C→EC c1] ∧ ,[C→EC c2])]
  [((or-c c1 c2)) `(,[C→EC c1] ∨ ,[C→EC c2])]
  [((μ-c x c)) `(μ ,x ,[C→EC c])]
  [((func-c cx cy _)) `(,@ (map C→EC cx) ↦ ,(C→EC cy))]
  [((struct-c t cs))
   `(,(string->symbol (string-append (symbol->string t) "/c")) ,@ [map C→EC cs])]
  [((op name)) name]
  [((struct-p t _)) (gen-p t)]
  [((f 1 (@ _ [op 'false?] (list [@ _ o (list [x 0])])) #f))
   `(¬ ,(match o
          [(op name) name]
          [(struct-p t _) t]))]
  [((f 1 (@ _ [ref _ _ name] (list (x 0))) #f)) name]
  [(v) v])


;; pretty printing for debugging
(define/match (show-ς s)
  [((ς E σ k)) `(,(show-E E) ,σ ,(show-κ k))])
(define/match (show-κ k)
  [('mt) 'mt]
  [((if/k E1 E2 k)) `(IF/K ,(show-E E1) ,(show-E E2) ,(show-κ k))]
  [((@/k _ Vs Es k)) `(@/K ,(map show-E Vs) ,(map show-E Es) ,(show-κ k))]
  [((mon/k _ _ _ C k)) `(MON/K ,(show-C C) ,(show-κ k))]
  [((vmon/k _ _ _ _ Cs Us k)) `(VMON/K ,(map show-C Cs) ,(map show-E Us) ,(show-κ k))])
(define/match (show-E E)
  [((close e _)) (show-e e)]
  [((val U _)) (show-U U)]
  [((Blm l+ lo)) `(Blame ,l+ ,lo)]
  [((? L? l)) `(L ,l)]
  [((Mon _ _ _ C E)) `(MON ,(show-C C) ,(show-E E))]
  [((Fmon _ C V)) `(FMON ,(show-C C) ,(show-E V))]
  [((Assume V C)) `(ASSUME ,(show-E V) ,(show-C C))])
(define/match (show-U U)
  [((close f _)) (show-e f)]
  [((•)) `•]
  [((Struct t Vs)) `(,t ,@ (map show-E Vs))]
  [((Arr _ _ _ C V)) `(=> ,(show-C C) ,(show-E V))]
  [((? b? b)) (show-b b)])
(define/match (show-C C)
  [((close c _)) (show-c c)])
(define/match (show-c c)
  [((func-c xs y _)) `(,@ (map show-c xs) ↦ ,(show-c y))]
  [((and-c c1 c2)) `(and/c ,(show-c c1) ,(show-c c2))]
  [((or-c c1 c2)) `(or/c ,(show-c c1) ,(show-c c2))]
  [((struct-c t cs))
   `(,(string->symbol (string-append (symbol->string t) "/c")) ,@ (map show-c cs))]
  [((μ-c x c)) `(μ ,x ,(show-c c))]
  [((? v? v)) (show-e v)])
(define/match (show-e e)
  [((f n e _)) `(λ ,n ,(show-e  e))]
  [((•)) '•]
  [((x sd)) `(x ,sd)]
  [((ref _ _ x)) x]
  [((@ _ f xs)) `(,(show-e f) ,@ (map show-e xs))]
  [((if/ e1 e2 e3)) `(if ,(show-e e1) ,(show-e e2) ,(show-e e3))]
  [((amb _)) 'amb]
  [((? b? b)) (show-b b)])
(define/match (show-b b)
  [((op name)) name]
  [((struct-mk t _)) t]
  [((struct-p t _))
   (string->symbol (string-append (symbol->string t) "?"))]
  [((struct-ac t n i))
   (string->symbol (string-append (symbol->string t) "-" (number->string i)))]
  [(b) b])