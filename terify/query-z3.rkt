#lang typed/racket/base

(require racket/match racket/list racket/set racket/string racket/bool racket/port racket/system
         "../utils.rkt" "../lang.rkt" "closure.rkt" "show.rkt")
(provide query model handled?)

; query external solver for provability relation
(: query : .σ .V .V → .R)
(define (query σ V C)
  (cond    
   [(not (handled? C)) 'Neither] ; skip when contract is strange
   [else
    #;(printf "Queried with: ~a~n~a~n" (show-Ans σ V) C)
    (define-values (σ′ i) (match V
                            [(.L i) (values σ i)]
                            [(? .//? V) (values (σ-set σ -1 V) -1) #|HACK|#]))
    (define-values (Q* i*) (explore σ′ (set-add (span-C C) i)))
    (define-values (q j*) (gen i C))
    #;(printf "premises [~a] involve labels [~a] ~n" Q* i*)
    (cond
     ;; Skip querying when the set of labels spanned by premises does not cover
     ;; That spanned by conclusion
     [(not (subset? j* i*)) 'Neither]
     ;; Skip querying when the set of labels spanned by premises only contains
     ;; The single label we ask about (relies on local provability relation
     ;; Being precise enough)
     [(equal? i* {set i}) 'Neither]
     ;; Skip querying when could not generate conclusion
     [(false? q) 'Neither]
     [else
      (call-with
       (string-append*
        (for/list ([i i*])
          (format "(declare-const ~a ~a)~n"
                  (→lab i)
                  (match-let ([(.// _ C*) (σ@ σ′ i)])
                    (or (for/or : (U #f Sym) ([C : .V C*] #:when (match? C (.// (.int?) _))) 'Int)
                        'Real)))))
       (string-append* (for/list ([q Q*]) (format "(assert ~a)~n" q)))
       q)])]))

(: handled? : .V → Bool)
(define (handled? C)
  (match? C
    (.// (.λ↓ (.λ 1 (.@ (? arith?) (list (.x 0) (or (.x _) (.b (? num?)))) _) #f) _) _)
    (.// (.λ↓ (.λ 1 (.@ (or (.=) (.equal?)) (list (.x 0) (or (.x _) (.b (? num?)))) _) #f) _) _)
    (.// (.λ↓ (.λ 1 (.@ (or (.=) (.equal?))
                        (list (.x 0)
                              (.@ (? arith?)
                                  (list (or (.x _) (.b (? num?)))
                                        (or (.x _) (.b (? num?)))) _)) _) #f) _) _)
    (.// (.St '¬/c (list (? handled? C′))) _)))

(: arith? : .e → Bool)
(define (arith? e)
  (match? e (.=) (.equal?) (.>) (.<) (.≥) (.≤)))

; generate all possible assertions spanned by given set of labels
; return set of assertions as wel as set of labels involved
(: explore : .σ (Setof Int) → (Values (Setof String) (Setof Int)))
(define (explore σ i*)
  (match-define (.σ m _) σ)
  (define asserts : (Setof String) ∅)
  (define seen : (Setof Int) ∅)
  (define involved : (Setof Int) ∅)  
  
  (: visit : Int → Void)
  (define (visit i)
    (unless (set-member? seen i)
      (match-let ([(and V (.// U C*)) (hash-ref m i)]
                  [queue (ann ∅ (Setof Int))])
        (when (match? U (.b (? real?)))
          (∪! asserts (format "(= ~a ~a)" (→lab i) (→lab V)))
          (∪! involved i))
        (for ([C C*])
          (let-values ([(q1 j*) (gen i C)])
            (∪! queue j*)
            (when (str? q1)
              (∪! asserts q1)
              (∪! involved j*))))
        (∪! seen i)
        (for ([j queue]) (visit j)))))
  (for ([i i*]) (visit i))
  
  (: involved? : (U .V (Listof .V)) → Boolean)
  (define (involved? V)
    (match V
      [(.L i) (set-member? involved i)]
      [(? list? l) (andmap involved? l)]
      [(.// U Cs)
       (match U
         [(.•) (or (set-member? Cs REAL/C) (set-member? Cs INT/C))]
         [(.b (? real?)) #t]
         [_ #f])]))
  
  ;; Constraint equal inputs -> equal outputs
  (for ([(i Vᵢ) (in-hash m)])
    (match-define (.// Uᵢ _) Vᵢ)
    (when (.Case? Uᵢ)
      (match-define (.Case mappings) Uᵢ)
      (let loop₁ : Void ([pairs : (Listof (Pairof (Listof .V) .L)) (hash->list mappings)])
        (when (cons? pairs)
          (match-define (cons (cons xs₁ y₁) pairs₂) pairs)
          (when (and (involved? xs₁) (involved? y₁))
            (let loop₂ : Void ([pairs₂ : (Listof (Pairof (Listof .V) .L)) pairs₂])
              (when (cons? pairs₂)
                (match-define (cons (cons xs₂ y₂) pairs₃) pairs₂)
                (when (and (involved? xs₂) (involved? y₂))
                  (∪!
                    asserts
                    (format
                     "~a"
                     `(=>
                       (and ,@(for/list : (Listof Any) ([x₁ xs₁] [x₂ xs₂])
                                `(= ,(→lab x₁) ,(→lab x₂))))
                       (= ,(→lab y₁) ,(→lab y₂))))))
                (loop₂ pairs₃))))
          (loop₁ pairs₂)))))
  
  (values asserts involved))

; generate statemetn expressing relationship between i and C
; e.g. <L0, (sum/c 1 2)>  translates to  "L0 = 1 + 2"
(: gen : Int .V → (Values (U #f String) (Setof Int)))
(define (gen i C)
  (match C
    [(.// (.λ↓ f ρ) _)
     (define ρ@*
       (match-lambda
        [(.b (? num? n)) (Prim n)]
        [(.x i) (ρ@ ρ (- i 1))]))
     (match f
       [(.λ 1 (.@ (? .o? o) (list (.x 0) (and e (or (.x _) (.b (? num?))))) _) #f)
        (define X (ρ@* e))
        (values (format "(~a ~a ~a)" (→lab o) (→lab i) (→lab X))
                (labels i X))]
       [(.λ 1 (.@ (or (.=) (.equal?))
                  (list (.x 0) (.@ (.sqrt) (list (and M (or (.x _) (.b (? real?))))) _)) _) _)
        (define X (ρ@* M))
        (values (format "(= ~a (^ ~a 0.5))" (→lab i) (→lab X))
                (labels i X))]
       [(.λ 1 (.@ (or (.=) (.equal?))
                  (list (.x 0) (.@ (? .o? o)
                                   (list (and M (or (.x _) (.b (? num?))))
                                         (and N (or (.x _) (.b (? num?))))) _)) _) #f)
        (define X (ρ@* M))
        (define Y (ρ@* N))
        (values (format "(= ~a (~a ~a ~a))" (→lab i) (→lab o) (→lab X) (→lab Y))
                (labels i X Y))]
       [_ (values #f ∅)])]
    [(.// (.St '¬/c (list D)) _)
     (define-values (q i*) (gen i D))
     (values (match q [(? str? s) (format "(not ~a)" s)] [_ #f]) i*)]
    [_ (values #f ∅)]))

; perform query/ies with given declarations, assertions, and conclusion,
; trying to decide whether value definitely proves or refutes predicate
(: call-with : String String String → .R)
(define (call-with decs asserts concl)
  (match (call (str++ decs asserts (format "(assert (not ~a))~n(check-sat)~n" concl)))
    [(regexp #rx"^unsat") 'Proved]
    [(regexp #rx"^sat") 
     (match (call (str++ decs asserts (format "(assert ~a)~n(check-sat)~n" concl)))
             [(regexp #rx"^unsat") 'Refuted]
             [_ #;(printf "Neither~n") 'Neither])]
    [_ #;(printf "Neither~n")'Neither]))

; performs system call to solver with given query
(: call : String → String)
(define (call query)
  #;(printf "Called with:~n~a~n~n" query)
  (with-output-to-string
   (λ () ; FIXME: lo-tech. I don't know Z3's exit code
     (system (format "echo \"~a\" | z3 -in -smt2" query)))))

; generate printable/readable element for given value/label index
(: →lab : (U Int .V .o) → (U Num String Sym))
(define →lab
  (match-lambda
    [(.// (.b (? real? x)) _) x]
    [(or (.L i) (? int? i))
     (if (int? i)
         (if (>= i 0) (format "L~a" i) (format "X~a" (- i)))
         (error "can't happen"))]
    [(.equal?) '=] [(.≥) '>=] [(.≤) '<=]
    [(? .o? o) (name o)]))

; extracts all labels in contract
(: span-C : .V → (Setof Int))
(define span-C
  (match-lambda
    [(.// (.λ↓ _ (.ρ m _)) _)
     (for/set: Int ([V (in-hash-values m)] #:when (.L? V))
       (match-let ([(.L i) V]) i))]
    [_ ∅]))

;; syntactic sugar
(define-syntax-rule (∪! s i)
  (set! s (let ([x i]) (if (set? x) (set-union s x) (set-add s i)))))
(: labels : (U .V Int) * → (Setof Int))
(define (labels . V*)
  (for/set: Int ([V V*] #:when (match? V (? int?) (.L _)))
    (match V
      [(? int? i) i]
      [(.L i) i])))

(: model : .σ → (Option .σ))
(define (model σ)
  (match-define (.σ m _) σ)
  (cond
   [(for/or : Any ([V (in-hash-values m)])
      (match-define (.// U _) V)
      (.•? U))
    (model′ σ)]
   [else σ]))

(: model′ : .σ → (Option .σ))
(define (model′ σ)
  ;; Compute all labels of reals/ints
  (define-values (labels types)
    (for/fold ([labels : (Listof Int) '()]
               [types : (Listof (U 'Int 'Real)) '()])
              ([(l V) (in-hash (.σ-map σ))])
      (match V
        [(.// U C*)
         (match U
           [(.b (? integer?)) (values (cons l labels) (cons 'Int types))]
           [(.b (? real?)) (values (cons l labels) (cons 'Real types))]
           [(.•)
            (cond
             [(for/or : Boolean ([C : .V C*]
                                 #:when (match? C (.// (.int?) _)))
                #t)
              (values (cons l labels) (cons 'Int types))]
             [(for/or : Boolean ([C : .V C*]
                                 #:when (match? C (.// (.real?) _)))
                #t)
              (values (cons l labels) (cons 'Real types))]
             [else (values labels types)])]
           [_ (values labels types)])]
        [_ (values labels types)])))
  #;(printf "labels:~n~a~n" labels)
  ;; Generate assertions
  (define-values (assertions _) (explore σ (list->set labels)))
  #;(printf "assertions:~n~a~n" assertions)
  ;; Generate query
  (define query
    (string-append
     ;; Declaration
     (string-append*
      (for/list ([l labels] [t types])
        (format "(declare-const ~a ~a)~n" (→lab l) t)))
     ;; Assertions
     (string-append*
      (for/list ([assrt assertions])
        (format "(assert ~a)~n" assrt)))
     ;; Generate model
     (format "(check-sat)~n(get-model)~n")))
  ;; Call to Z3
  #;(printf "Query:~n~a~n" query)
  (match (call query)
    [(regexp #rx"^sat(.*)" (list _ (? string? m/str)))
     (match-define (.σ m l) σ)
     (with-input-from-string m/str
       (λ ()
         (cast
          (match (read)
           [(list 'model lines ...)
            #;(begin
              (printf "Model:~n")
              (for ([l lines]) (printf "~a~n" l)))
            (match-define (.σ m l) σ)
            (define m′
              (for/fold ([m : (Map Int .//) m])
                        ([line : Any (in-list lines)])
                (match-define `(define-fun ,(? symbol? a) () ,_ ,e) line)
                #;(printf "e: ~a~n" e)
                (define res : Real
                  (match e
                    [`(+ ,(? real? x) ,(? real? y) ...)
                     (apply + x (cast y (Listof Real)))]
                    [`(- ,(? real? x) ,(? real? y) ...)
                     (apply - x (cast y (Listof Real)))]
                    [`(* ,(? real? x) ,(? real? y) ...)
                     (apply * x (cast y (Listof Real)))]
                    [`(/ ,(? real? x) ,(? real? y) ...)
                     (apply / x (cast y (Listof Real)))]
                    [(? real? x) x]))
                (hash-set m (lab→i a) (.// (.b (cast res Real)) ∅))))
            ;; Fixup. Z3 gives empty model sometimes for trivial cases
            (define m′′
              (for/hash : (Map Integer .//) ([(k v) m′])
                (values
                 k
                 (match v
                   [(.// (.•) _) (Prim 0)]
                   [_ v]))))
            (.σ m′′ l)])
          .σ)))]
    [_ #f]))

(: lab→i : Symbol → Int)
(define (lab→i s)
  (match (symbol->string s)
    [(regexp #rx"L(.+)" (list _ (? string? d)))
     (cast (string->number d) Int)]
    [(regexp #rx"X(.+)" (list _ (? string? d)))
     (- (cast (string->number d) Int))]))
