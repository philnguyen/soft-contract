#lang typed/racket

(provide (all-defined-out)) ; TODO

(: memoize : (∀ (X Y) ((X → Y) [#:eq? Bool] → (X → Y))))
(define (memoize f #:eq? [eq?? #f])
  (let: ([m : (Map X Y) ((if eq?? make-hasheq make-hash))])
    (λ (x) (hash-ref! m x (λ () (f x))))))


;; define data-type hierarchy
(define-syntax-rule
  (define-data (k f ...) ki ...)
  (begin
    (struct: k (f ...) #:transparent)
    (define-data-under k ki) ...))
(define-syntax define-data-under
  (syntax-rules (subset:)
    [(_ k (subset: (ki fi ...) cl ...))
     (begin
       (struct: ki k (fi ...) #:transparent)
       (define-data-under ki cl) ...)]
    [(_ k (ki fi ...)) (struct: ki k (fi ...) #:transparent)]))

(define-syntax-rule (match? v p ...) (match v [p #t] ... [_ #f]))
(define-syntax-rule (match-λ? p ...) (match-lambda [p #t] ... [_ #f]))

(define-syntax-rule (for/set: X (c ...) e ...)
  (for/fold: ([acc : (Setof X) ∅]) (c ...)
    (set-add acc (begin e ...))))

;; non-deterministic match. The types is to make it less awkard in pattern matching
(define-syntax match/nd:
  (syntax-rules (→)
    [(_ (α → β) v [p e ...] ...)
     (let: ([x v]
            [f : (α → (U β (Setof β))) (match-lambda [p e ...] ... [x (error "match/nd unmatched: " x)])])
       (if (set? x)
           (for/fold: : (Setof β) ([acc : (Setof β) ∅]) ([xi x])
             (let ([y (f xi)])
               (if (set? y) (set-union acc y) (set-add acc y))))
           (f x)))]))

;; define the same type for multiple identifiers
(define-syntax :*
  (syntax-rules (:)
    [(_ (id ...) : rest ...) (begin (: id : rest ...) ...)]))

(define-syntax-rule (define** [id v] ...) (define-values (id ...) (values v ...)))

;; Abbreviations
(define: ∅ : (Setof Nothing) (set))
(define-type Int Integer)
(define-type Map HashTable)
(define-type (MMap X Y) (Map X (Setof Y)))
(define-type Num Number)
(define-type Bool Boolean)
(define-type Sym Symbol)
(define-type Str String)
(define**
  [int? integer?] [num? number?] [str? string?] [sym? symbol?] [bool? boolean?]
  [sym→str symbol->string] [num→str number->string] [str→sym string->symbol]
  [str++ string-append])

;; evaluate an expression within given #seconds
;; return singleton list of value, or #f on timeout
(define-syntax-rule (within-time: τ n e ...)
  (let: ([c : (Channelof (U #f (List τ))) (make-channel)])
    (let ([t1 (thread (λ () (channel-put c (list (begin e ...)))))]
          [t2 (thread (λ () (sleep n) (channel-put c #f)))])
      (match (channel-get c)
        [#f (kill-thread t1) #f]
        [ans (kill-thread t2) ans]))))

(: mmap-join! : (∀ (X Y) ((MMap X Y) X Y → Void)))
(define (mmap-join! m x y)
  (hash-update! m x (λ: ([s : (Setof Y)]) (set-add s y)) (λ () ∅)))

(: mmap-join : (∀ (X Y) ((MMap X Y) X Y → (MMap X Y))))
(define (mmap-join m x y)
  (hash-update m x (λ: ([s : (Setof Y)]) (set-add s y)) (λ () ∅)))

(define-syntax-rule (dbg n (f x ...))
  (begin
    (printf "~a:~a~nof~n~a~n" n 'f (list x ...))
    (let ([y (f x ...)])
      (printf "is~n~a~n~n" y)
      y))
  #;(let ([y (f x ...)])
      (printf "~a:~a~nof~n~a~nis~n~a~n~n" n 'f (list x ...) y)
      y))
(define-syntax-rule (dbg/off n (f x ...)) (f x ...))

(define-syntax-rule (define-set: s : τ [in? add!])
  (begin
    (define: s : (Setof τ) ∅)
    (: in? : τ → Bool)
    (define (in? x) (set-member? s x))
    (: add! : (U τ (Setof τ)) → Void)
    (define (add! x) (set! s (if (set? x) (set-union s x) (set-add s x))))))