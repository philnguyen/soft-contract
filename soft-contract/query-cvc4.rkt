#lang typed/racket/base

(require racket/match racket/list racket/set racket/bool racket/string racket/port racket/system
         "utils.rkt" "lang.rkt" "runtime.rkt" "show.rkt")
(provide query handled?)

; query external solver for provability relation
(: query : .σ .V .V → .R)
(define (query σ V C)
  (cond    
    [(not (handled? C)) '?] ; skip when contract is strange
    [else
     #;(log-debug "Queried with: ~a~n~a~n" (show-Ans σ V) C)
     (let*-values ([(σ′ i) (match V
                             [(.L i) (values σ i)]
                             [(? .//? V) (values (σ-set σ -1 V) -1) #|HACK|#])]
                   [(Q* i*) (explore σ′ (set-add (span-C C) i))]
                   [(q j*) (gen i C)])
       #;(log-debug "premises [~a] involve labels [~a] ~n" Q* i*)
       (cond
         ; skip querying when the set of labels spanned by premises does not cover
         ; that spanned by conclusion
         [(not (subset? j* i*)) '?]
         ; skip querying when the set of labels spanned by premises only contains
         ; the single label we ask about (relies on local provability relation
         ; being precise enough)
         [(equal? i* {set i}) '?]
         ; skip querying when could not generate conclusion
         [(false? q) '?]
         [else
          (call-with
           (string-append*
            (for/list ([i i*])
              (format "~a:~a;~n"
                      (→lab i)
                      (match-let ([(.// _ C*) (σ@ σ′ i)])
                        (or (for/or : (U #f Symbol) ([C : .V C*] #:when (match? C (.// 'integer? _))) 'INT)
                            'REAL)))))
           (string-append* (for/list ([q Q*]) (format "ASSERT ~a;~n" q)))
           q)]))]))

(: handled? : .V → Boolean)
(define (handled? C)
  (match? C
    (.// (.λ↓ (.λ 1 (.@ (? arith?) (list (.x 0) (or (.x _) (.b (? number?)))) _)) _) _)
    (.// (.λ↓ (.λ 1 (.@ (or '= 'equal?) (list (.x 0) (or (.x _) (.b (? number?)))) _)) _) _)
    (.// (.λ↓ (.λ 1 (.@ (or '= 'equal?)
                        (list (.x 0)
                              (.@ (? arith?)
                                  (list (or (.x _) (.b (? number?)))
                                        (or (.x _) (.b (? number?)))) _)) _)) _) _)
    (.// (.St 'not/c (list (? handled? C′))) _)))

(: arith? : .expr → Boolean)
(define (arith? e)
  (match? e '= 'equal? '> '< '>= '<=))

; generate all possible assertions spanned by given set of labels
; return set of assertions as wel as set of labels involved
(: explore : .σ (Setof Integer) → (Values (Setof String) (Setof Integer)))
(define (explore σ i*)
  #;(log-debug "explore:~n~nσ:~n~a~n~ni*:~n~a~n~n~n" σ i*)
  (define-set asserts : String)
  (define-set seen : Integer)
  (define-set involved : Integer)
  
  (: visit : Integer → Void)
  (define (visit i)
    (unless (seen-has? i)
      (match-define (and V (.// U C*)) (σ@ σ i))
      (define queue : (Setof Integer) ∅)
      (when (real? U)
        (asserts-add! (format "~a = ~a" (→lab i) (→lab V)))
        (involved-add! i))
      (for ([C C*])
        (let-values ([(q1 j*) (gen i C)])
          (set! queue (set-union queue j*))
          (when (string? q1)
            (asserts-add! q1)
            (involved-add! j*))))
      (seen-add! i)
      (for ([j queue]) (visit j))))
  (for ([i i*]) (visit i))
  (values asserts involved))

; generate statemetn expressing relationship between i and C
; e.g. <L0, (sum/c 1 2)>  translates to  "L0 = 1 + 2"
(: gen : Integer .V → (Values (U #f String) (Setof Integer)))
(define (gen i C)
  (match C
    [(.// (.λ↓ f ρ) _)
     (let ([ρ@* (match-lambda
                  [(.b (? number? n)) (Prim n)]
                  [(.x i) (ρ@ ρ (- i 1))])])
       (match f
         [(.λ 1 (.@ (? .o? o) (list (.x 0) (and e (or (.x _) (.b (? number?))))) _))
          (let ([X (ρ@* e)])
            (values (format "~a ~a ~a" (→lab i) (→lab o) (→lab X))
                    (labels i X)))]
         [(.λ 1 (.@ (or '= 'equal?)
                    (list (.x 0) (.@ 'sqrt (list (and M (or (.x _) (.b (? real?))))) _)) _))
          (let ([X (ρ@* M)])
            (values (format "~a = ~a ^ 0.5" (→lab i) (→lab X))
                    (labels i X)))]
         [(.λ 1 (.@ (or '= 'equal?)
                    (list (.x 0) (.@ (? .o? o)
                                     (list (and M (or (.x _) (.b (? number?))))
                                           (and N (or (.x _) (.b (? number?))))) _)) _))
          (let ([X (ρ@* M)] [Y (ρ@* N)])
            (values (format "~a = ~a ~a ~a" (→lab i) (→lab X) (→lab o) (→lab Y))
                    (labels i X Y)))]
         [_ (values #f ∅)]))]
    [(.// (.St 'not/c (list D)) _)
     (let-values ([(q i*) (gen i D)])
       (values (match q [(? string? s) (format "NOT (~a)" s)] [_ #f]) i*))]
    [_ (values #f ∅)]))

; perform query/ies with given declarations, assertions, and conclusion,
; trying to decide whether value definitely proves or refutes predicate
(: call-with : String String String → .R)
(define (call-with decs asserts concl)
  (match (call (format "~a~n~a~nQUERY ~a;~n" decs asserts concl))
    [(regexp #rx"^valid") '✓]
    [(regexp #rx"^invalid")
     (match (call (format "~a~n~a~nCHECKSAT ~a;" decs asserts concl))
          [(regexp #rx"^unsat") 'X]
          [_ #;(log-debug "?~n") '?])]
    [_ #;(log-debug "?~n")'?]))

; performs system call to solver with given query
(: call : String → String)
(define (call query)
  #;(log-debug "Called with:~n~a~n~n" query)
  (with-output-to-string
   (λ () ; CVC4 from 1.3 no longer uses exit code to indicate sat/unsat
     (system (format "echo \"~a\" | cvc4 -q" query)))))

; generate printable/readable element for given value/label index
(: →lab : (U Integer .V .o) → (U Number String Symbol))
(define →lab
  (match-lambda
    [(.// (.b (? real? x)) _) x]
    [(or (.L i) (? integer? i))
     (if (integer? i) (if (>= i 0) (format "L~a" i) (format "X~a" (- -1 i)))
         (error "can't happen"))]
    [(? symbol? o) o]))

; extracts all labels in contract
(: span-C : .V → (Setof Integer))
(define span-C
  (match-lambda
    [(.// (.λ↓ _ (.ρ m _)) _)
     (for/set: : (Setof Integer) ([V (in-hash-values m)] #:when (.L? V))
       (match-let ([(.L i) V]) i))]
    [_ ∅]))

;; syntactic sugar

(: labels : (U .V Integer) * → (Setof Integer))
(define (labels . V*)
  (for/set: : (Setof Integer) ([V V*] #:when (match? V (? integer?) (.L _)))
    (match V
      [(? integer? i) i]
      [(.L i) i])))


