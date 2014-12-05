#lang typed/racket/base
(require racket/match racket/set racket/string racket/port
         "../utils.rkt" "../lang.rkt" "runtime.rkt" "../query-z3.rkt")
(provide model
         (all-from-out "../query-z3.rkt"))

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
              (for/fold ([m : (Map Int .V+) m])
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
              (for/hash : (Map Integer .V+) ([(k v) m′])
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
