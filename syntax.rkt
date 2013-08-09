#lang racket
(provide ∅ nd/c nd# non-det if/nd match/nd match? ∪ within-time define/memo debug)

(define ∅ (set))

;; ∀X ≠ Set, X* = X ∪ (Setof X)
(define ((nd/c p) x)
  (if (p x) (not (set? x)) ((set/c p) x)))

;; X* -> Integer
(define (nd# x*)
  (if (set? x*) (set-count x*) 1))
 
;; (X -> Y*) X* -> Y*
(define (non-det f x*)
  (cond
    [(set? x*) (for/fold ([acc ∅]) ([x x*]) (∪1 acc (f x)))]
    [else (f x*)]))

;; non-deterministic versions of conditionals
(define-syntax-rule (if/nd e e1 e2)
  (match/nd e [#f e2] [_ e1]))
(define-syntax-rule (match/nd v [p e ...] ...)
  (non-det (match-lambda [p e ...] ...) v))

;; Racket has this in unstable/match
(define-syntax-rule (match? v p ...)
  (match v [p #t] ... [_ #f]))

;; ∪ : X* ... -> X*
(define (∪ . xs)
  (match xs ; special cases for efficiency
    ['() ∅]
    [(list x) x]
    [_ (for/fold ([acc ∅]) ([x xs]) (∪1 acc x))]))

;; (Setof X) X* -> (Setof X)
(define (∪1 xs x*)
  ((if (set? x*) set-union set-add) xs x*))

;; evaluate a expression within given number of seconds
;; return singleton list of value or #f
(define-syntax-rule (within-time n e ...)
  (let ([c (make-channel)])
    (let ([t1 (thread (λ () (channel-put c (list (begin e ...)))))]
          [t2 (thread (λ () (sleep n) (channel-put c #f)))])
      (match (channel-get c)
        [#f (kill-thread t1) #f]
        [ans (kill-thread t2) ans]))))

(define-syntax-rule (define/memo (f x ...) e ...)
  (define f
    (let ([m (make-hash)])
      (λ (x ...) (hash-ref! m (list x ...) (λ () e ...))))))

(define-syntax-rule (debug f s ...)
  (printf f s ...)
  #;(void))