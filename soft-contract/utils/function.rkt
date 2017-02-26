#lang typed/racket/base

(provide (all-defined-out))

(require (for-syntax racket/base racket/syntax syntax/parse))

(: fix : (∀ (X) (X → X) X → X))
;; Compute `f`'s fixpoint starting from `x`
(define (fix f x)
  (define x* (f x))
  (if (equal? x x*) x (fix f x*)))

(define-syntax-rule (apply/values f x)
  (call-with-values (λ () x) f))

(define memo-data : (HashTable Symbol HashTableTop) (make-hasheq))

(: find-memo-key ([Any] [(Option Symbol)] . ->* . Any))
(define (find-memo-key v [k #f])
  
  (: search : HashTableTop → Any)
  (define (search m)
    (for/or ([(k* v*) (in-hash m)] #:when (equal? k* k)) v*))

  (cond [k (search (hash-ref memo-data k))]
        [else (for/or ([(k* m*) (in-hash memo-data)]) (search m*))]))

(define-syntax define/memo
  (syntax-rules (:)
    [(_ (f [x : X]) : Y e ...)
     (define f : (X → Y)
       (let ([m : (HashTable X Y) (make-hash)])
         (hash-set! memo-data 'f m)
         (λ ([x : X])
           (hash-ref! m x (λ () : Y e ...)))))]
    [(_ (f [x : X] ...) : Y e ...)
     (define f : (X ... → Y)
       (let ([m : (HashTable (List X ...) Y) (make-hash)])
         (hash-set! memo-data 'f m)
         (λ ([x : X] ...)
           (hash-ref! m (list x ...) (λ () : Y e ...)))))]))

(define-syntax define/memoeq
  (syntax-rules (:)
    [(_ (f [x : X]) : Y e ...)
     (define f : (X → Y)
       (let ([m : (HashTable X Y) (make-hasheq)])
         (hash-set! memo-data 'f m)
         (λ ([x : X])
           (hash-ref! m x (λ () : Y e ...)))))]))

(: memoize (∀ (X Y) (X → Y) → X → Y))
(define (memoize f)
  (let ([m : (HashTable X Y) (make-hash)])
    (λ (x)
      (hash-ref! m x (λ () (f x))))))

(: memoizeeq (∀ (X Y) (X → Y) → X → Y))
(define (memoizeeq f)
  (let ([m : (HashTable X Y) (make-hasheq)])
    (λ (x)
      (hash-ref! m x (λ () (f x))))))

(define (dump-memo-info) : Void
  (for ([(f m) memo-data])
    (printf "~a : ~a~n" f (hash-count m))))
