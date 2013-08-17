#lang racket
(require "lang.rkt" "syntax.rkt" "show.rkt")
(provide
 (contract-out
  [query (σ? V? C? . -> . (or/c 'Proved 'Refuted 'Neither))]))

;; queries external solver for provability relation
(define (query σ V C)
  (let*-values ([(σ1 L) (if (L? V) (values σ V)
                            (values (σ-set σ -1 V) -1) #|HACK|#)]
                [(Qs Ls) (explore σ (∪ L (C->Ls C)))])
    (cond
      [(set-empty? Qs) 'Neither] ; avoid I/O on absolutely no information
      [else (call-with
             (string-append*
              (for/list ([L Ls])
                (format "~a:~a;~n"
                        (V->lab L)
                        (match-let ([(val _ Cs) (σ@ σ L)])
                          (or (for/first ([C Cs] #:when (match? C (close (op 'int?) _))) 'INT)
                              'REAL)))))
             (string-append* (for/list ([q Qs]) (format "ASSERT ~a;~n" q)))
             (let-values ([(q _) (gen L C)]) q))])))

;; generates all possible assertions spanned by given set of labels
;; returns set of assertions as well as set of labels involved
(define (explore σ Ls)
  (define-values (asserts seen) (values ∅ ∅))
  
  ; L -> Void
  (define (visit L)
    (unless (set-member? seen L)
      (match-let ([(and V (val U Ds)) (σ@ σ L)]
                  [queue ∅])
        (when (real? U)
          (∪! asserts (format "~a = ~a" (V->lab L) (V->lab V))))
        (for ([D Ds])
          (let-values ([(q1 Ls1) (gen L D)])
            (∪! queue Ls1)
            (∪! asserts q1)))
        (∪! seen L)
        (for ([Lq queue]) (visit Lq)))))
  
  (for ([L Ls]) (visit L))
  (values asserts seen))

;; generates statement expressing relationship between L and C
;; e.g. [L0 ↦ (sum/c 1 2))  gives  "L0 = 1 + 2"
(define (gen L C)
  (match-let ([(close c ρ) C])
    (let ([ρ@* (match-lambda
                 [(? number? n) (val n ∅)]
                 [(x sd) (ρ@ ρ (- sd 1))])])
      (match c
        [(f 1 (@ _ (op o) (list (x 0) (and e (or (? x?) (? number?))))) #f)
         (let ([X (ρ@* e)])
           (values (format "~a ~a ~a" (V->lab L) (->o o) (V->lab X))
                   (take-labels L X)))]
        [(f 1 (@ _ (op (or '= 'equal?))
                 (list (x 0) (@ _ (op o)
                                (list (and e1 (or (? x?) (? number?)))
                                      (and e2 (or (? x?) (? number?))))))) #f)
         (let ([X1 (ρ@* e1)] [X2 (ρ@* e2)])
           (values (format "~a = ~a ~a ~a" (V->lab L) (V->lab X1) (->o o) (V->lab X2))
                   (take-labels X1 X2)))]
        [(f 1 (@ _ (op 'false?) (list e)) #f)
         (let-values ([(q Ls) (gen L (close (f 1 e #f) ρ))])
           (values (match/nd q [(? string? s) (format "NOT (~a)" s)]) Ls))]
        [_ #;(printf "misc: ~a~n~n" C) (values ∅ ∅)]))))

;; perform query/ies with given declarations, assertions, and conclusion,
;; trying to decide whether value definitely proves or refutes predicate
(define (call-with decs asserts concl)
  (match (call (string-append decs asserts (format "QUERY ~a;~n" concl)))
    [20 'Proved] ; (asserts => concl) is valid
    [10 (match (call (string-append decs asserts (format "ASSERT ~a; CHECKSAT;" concl)))
          [20 'Refuted] ; (asserts ∧ concl) is unsat
          [_ 'Neither])]
    [_ 'Neither]))

;; performs system call to external solver with given query
(define (call query)
  #;(debug "Called with:~n~a~n~n" query)
  (system/exit-code (format "echo \"~a\" | cvc4 -q > /dev/null" query)))

;; generates printable/readable element for given value/label
(define/match (V->lab V)
  [((val (? real? n) _)) n]
  [((? L? L)) (if (>= L 0) (format "L~a" L) (format "X~a" (- L 1)))])

;; generates printable element for given operator name
(define/match (->o o)
  [('equal?) '=]
  [(_) o])

;; extracts all labels in contract
(define (C->Ls C)
  (match-let ([(close _ (ρ m _)) C])
    (for/set ([L (in-hash-values m)] #:when (L? L)) L)))

;; syntactic sugar
(define-syntax-rule (∪! s x) (set! s (∪ s x)))
(define (take-labels . xs) (for/set ([x xs] #:when (L? x)) x))
