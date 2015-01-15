#lang typed/racket/base
(require racket/match racket/set racket/string racket/port
         "../utils.rkt" "../lang.rkt" "../runtime.rkt" "../query-z3.rkt" "../provability.rkt" "../show.rkt")
(provide model σ•?)

(: model : .p .σ → (Option .σ))
;; Return one instantiation of program×heap
(define (model p σ)
  #;(printf "σ₀:~n~a~n" (show-σ σ))
  (cond
   [(σ•? σ)
    (define σ′ (model/z3 σ))
    (cond [σ′ #;(printf "σ₁:~n~a~n" (show-σ σ′)) (model/σ p σ′)]
          [else #f])]
   [else σ]))

(: model/σ : .p .σ → .σ)
;; Instantiate non-number abstract values
(define (model/σ p σ)
  
  (: model/v : .V+ → .V+)
  (define (model/v V)
    (match-define (.// U₁ Cs) V)
    (match U₁
      ['•
       (cond
        [(set-member? Cs INT/C)
         (error 'Internal "expect Z3 to have instantated `integer?`")
         V]
        [(set-member? Cs REAL/C)
         (error 'Internal "expect Z3 to have instanted `real?`")
         V]
        [(set-member? Cs NUM/C)
         (match (C*⇒C Cs REAL/C)
           ['Refuted (Prim +1i)]
           [_ (Prim (random))])]
        [(set-member? Cs STR/C)
         ;; FIXME: abstract string should have a `string-length` field
         ;; Currently, (string-length x) would be an integer somewhere on the heap
         (or
          (for/or : (U #f .V+)
                  ([C Cs]
                   #:when
                   (match? C (.// (.λ↓ (.λ 1 (.@ 'string-length (list (.x 0) (or (? .b?) (? .x?))) _) _) _) _)))
            (match-define (.// (.λ↓ (.λ _ (.@ _ (list _ len) _) _) ρ) _) C)
            (define n
              (match len
                [(.b (? exact-integer? n)) n]
                [(.x sd)
                 (define Vₗ (ρ@ ρ (- sd 1)))
                 (match Vₗ
                   [(.// (.b (? exact-integer? n)) _) n]
                   [(.L α)
                    (match (σ@ σ α)
                      [(.// (.b (? exact-integer? n)) _) n]
                      [V (error 'Internal "string-length is not an integer" V)])])]))
            (Prim (random-string n)))
          (Prim (random-string (random 16))))] 
        [(set-member? Cs (Prim 'boolean?))
         (match (C*⇒C Cs (Prim 'false?))
           ['Refuted
            (match (C*⇒C Cs (Prim 'true?))
              ['Refuted (error 'Internal "spurious path: boolean neither true nor false")]
              [_ (Prim #t)])]
           [_ (Prim #f)])]
        [(set-member? Cs PROC/C)
         (cond
          [(for/or : (U Boolean .V)
                   ([C Cs]
                    #:when
                    (match?
                     C
                     (.// (.λ↓ (.λ 1 (.@ 'arity=? (list (.x 0) _) _) _) _) _)))
             C)
           =>
           (λ ([C : (U Boolean .V)])
             (match-define
              (.// (.λ↓ (.λ 1 (.@ 'arity=? (list _ (.b (? exact-integer? n))) _) _) _) _)
              C)
             (→V (.λ↓ (.λ n (.b (random)) #f) ρ∅)))]
          [(for/or : (U Boolean .V)
                   ([C Cs]
                    #:when
                    (match?
                     C
                     (.// (.λ↓ (.λ 1 (.@ 'arity-includes? (list (.x 0) _) _) _) _) _)))
             C)
           =>
           (λ ([C : (U Boolean .V)])
             (match-define
              (.// (.λ↓ (.λ _ (.@ 'arity-includes? (list _ (.b (? exact-integer? n))) _) _) _) _)
              C)
             (→V (.λ↓ (.λ n (.b (random)) #f) ρ∅)))]
          [else (→V (.λ↓ (.λ 1 (.b (random)) #f) ρ∅))])]
        [else (→V (.St 'struct● (list (Prim (random)))))])]
      [(.λ↓ (.λ 1 (.@ (.•ₗ l) (list e) _) #f) ρ)
       (match-define (.// _ Cs) (σ@ σ l))
       (cond [(set-empty? Cs) (→V (.λ↓ (.λ 1 e #f) ρ))]
             [else V])]
      [_ V]))
  
  (match-define (.σ m l) σ)
  
  (define m′
    (for/hash : (Map Integer .V+) ([(L V) m])
      (values L (model/v V))))

  (.σ m′ l))

(: model/z3 : .σ → (Option .σ))
;; Ask Z3 to instantiate abstract values
(define (model/z3 σ)
  ;; Compute all labels of reals/ints
  (define-values (labels types)
    (for/fold ([labels : (Listof Integer) '()]
               [types : (Listof (U 'Int 'Real)) '()])
              ([(l V) (in-hash (.σ-map σ))])
      (match V
        [(.// U Cs)
         (match U
           [(.b (? integer?)) (values (cons l labels) (cons 'Int types))]
           [(.b (? real?)) (values (cons l labels) (cons 'Real types))]
           ['•
            (cond
             [(set-member? Cs INT/C)
              (values (cons l labels) (cons 'Int types))]
             [(set-member? Cs REAL/C)
              (values (cons l labels) (cons 'Real types))]
             [else (values labels types)])]
           [_ (values labels types)])]
        [_ (values labels types)])))
  #;(printf "labels:~n~a~n" labels)
  ;; Generate assertions
  (define-values (assertions _) (explore σ (list->set labels)))
  #;(printf "store:~n~a~n" (parameterize ([abstract-V? #f]) (show-σ σ)))
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
  #;(printf "Heap:~n~a~n" (show-σ σ))
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
              (for/fold ([m : (Map Integer .V+) m])
                        ([line : Any (in-list lines)])
                (match-define `(define-fun ,(? symbol? a) () ,_ ,e) line)
                #;(printf "e: ~a~n" e)
                (define res
                  (let go : Real ([e : Any e])
                    (match e
                      [`(+ ,eᵢ ...) (apply + (map go eᵢ))]
                      [`(- ,e₁ ,eᵢ ...) (apply - (go e₁) (map go eᵢ))]
                      [`(* ,eᵢ ...) (apply * (map go eᵢ))]
                      [`(/ ,e₁ ,eᵢ ...) (apply / (go e₁) (map go eᵢ))]
                      [`(,(or '^ '** 'expt) ,e₁ ,e₂) (assert (expt (go e₁) (go e₂)) real?)]
                      [(? real? x) x])))
                (hash-set m (lab→i a) (.// (.b res) ∅))))
            (.σ m′ l)])
          .σ)))]
    [_ #f]))

(: lab→i : Symbol → Integer)
(define (lab→i s)
  (match (symbol->string s)
    [(regexp #rx"L(.+)" (list _ (? string? d)))
     (cast (string->number d) Integer)]
    [(regexp #rx"X(.+)" (list _ (? string? d)))
     (- (cast (string->number d) Integer))]))

(: σ•? : .σ → Boolean)
;; Check if the heap has at least one abstract value
(define (σ•? σ)
  (match-define (.σ m _) σ)
  (for/or : Boolean ([V (in-hash-values m)])
    (match-define (.// U _) V)
    (.•? U)))

(: random-string : Integer → String)
(define random-string
  (let* ([chars "ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz0123456789"]
         [chars-count (string-length chars)])
    (λ (n)
      (list->string
       (for/list ([i (in-range n)])
         (string-ref chars (random chars-count)))))))
