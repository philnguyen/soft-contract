#lang racket
(require "lang.rkt" "syntax.rkt")
(provide
 (contract-out
  [query (σ? V? C? . -> . (or/c 'Proved 'Refuted 'Neither))]))

(define (query σ V C)
  (match V
    [(? L? L) (call (gen-queries σ L C))]
    [_ 'Neither]))

(define/contract (gen-queries σ L C)
  (σ? L? C? . -> . string?)
  
  ;; generate assertions and labels
  (define seen ∅)
  (define queries ∅)
  (define (visit L)
    (when (and (not (set-member? seen L)) (L? L))
      (define Ls ∅)
      (match-let ([(val U Cs) (σ@ σ L)])
        (when (real? U)
          (∪! queries (format "~a = ~a" (->L L) U)))
        (for ([Ci Cs])
          (let-values ([(qs1 Ls1) (gen L Ci)])
            (∪! queries qs1)
            (∪! Ls Ls1))))
      (∪! seen L)
      (for ([L Ls]) (visit L))))
  
  (visit L)
  
  (let-values ([(qn Ln) (gen L C)])
    (for ([L Ln]) (visit L))
    #;(begin
      (debug "qn: ~a~n" qn)
      (debug "C: ~a~n" C))
    (string-append
     (apply string-append
            (for/list ([L seen] #:when (L? L)) (format "~a : REAL;~n" (->L L))))
     #;(format "~a : REAL;~n" ; cvc4 has problem with really long declaration lines
             (string-join (for/list ([L seen] #:when (L? L)) (->L L)) ","))
     (apply string-append (for/list ([q queries]) (format "ASSERT ~a;~n" q)))
     (format "QUERY ~a;" qn))))

(define (gen L C)
  (match-let ([(close c ρ) C])
    (match c
      [(f 1 (@ _ (op o) (list (x 0) (? number? n))) #f)
       (values (format "~a ~a ~a" (->L L) (->o o) n) ∅)]
      [(f 1 (@ _ (op o) (list (x 0) (x sd))) #f)
       (match (ρ@ ρ (- sd 1))
         [V2
          (values (format "~a ~a ~a" (->L L) (->o o) (->V V2))
                  {set V2})]
         [_ (values ∅ ∅)])]
      [(f 1 (@ _ (op (or '= 'equal?)) (list (x 0) (@ _ (op o+) (list (x sd1) (x sd2))))) #f)
       (match* ((ρ@ ρ (- sd1 1)) (ρ@ ρ (- sd2 1)))
         [(V1 V2)
          (values (format "~a = ~a ~a ~a" (->L L) (->V V1) (->o o+) (->V V2)) {set V1 V2})])]
      [(f 1 (@ _ (op (or '= 'equal?)) (list (x 0) (@ _ (op o+) (list (x sd1) (? number? n))))) #f)
       (match (ρ@ ρ (- sd1 1))
         [V1 (values (format "~a = ~a ~a ~a" (->L L) (->V V1) (->o o+) n) {set V1})])]
      [(f 1 (@ _ (op (or '= 'equal?)) (list (x 0) (@ _ (op o+) (list (? number? n) (x sd2))))) #f)
       (match (ρ@ ρ (- sd2 1))
         [V2 (values (format "~a = ~a ~a ~a" (->L L) n (->o o+) (->V V2)) {set V2})])]
      [(f 1 (@ _ (op (or '= 'equal?)) (list (x 0) (@ _ (op 'add1) (list v)))) #f)
       (gen L (close (f 1 (@ 'Δ (op (or '= 'equal?)) (list (x 0) (@ 'Δ (op '+) (list v 1)))) #f) ρ))]
      [(f 1 (@ _ (op (or '= 'equal?)) (list (x 0) (@ _ (op 'sub1) (list v)))) #f)
       (gen L (close (f 1 (@ 'Δ (op (or '= 'equal?)) (list (x 0) (@ 'Δ (op '-) (list v 1)))) #f) ρ))]
      [(op 'positive?) (values (format "~a > 0" (->L L)) ∅)]
      [(op 'negative?) (values (format "~a < 0" (->L L)) ∅)]
      [(f 1 (@ _ (op 'false?) (list (@ _ (op 'positive?) (list (x 0))))) #f)
       (values (format "~a <= 0" (->L L)) ∅)]
      [(f 1 (@ _ (op 'false?) (list (@ _ (op 'negative?) (list (x 0))))) #f)
       (values (format "~a >= 0" (->L L)) ∅)]
      [_ (values ∅ ∅)])))

(define/match (->V V)
  [((? L? L)) (->L L)]
  [((val (? number? n) _)) n])

(define (->L L)
  (string-append "L" (number->string L)))

(define/match (->o o)
  [('equal?) '=]
  [(_) o])

(define (call query)
  (debug "Called with:~n~a~n~n" query)
  (match (system/exit-code (format "echo \"~a\" | cvc4 -q > /dev/null" query))
    [20 'Proved]
    [_ 'Neither]))

(define/match (->label l)
  [((list (? L? L))) (string-append "L" (number->string L))]
  [((? number? n)) n]
  [((? string? s)) (string-append "L" s)]
  [((? symbol? s)) (string-append "L" (symbol->string s))])

(define-syntax-rule (∪! s x)
  (set! s (∪ s x)))