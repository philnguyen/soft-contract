#lang typed/racket/base
(require racket/set racket/match racket/list racket/pretty racket/string racket/port)
(require (for-syntax racket/base racket/syntax syntax/parse))
(provide (all-defined-out)) ; TODO
(require/typed
 redex/reduction-semantics
 [variables-not-in (Any Any → (Listof Symbol))])

(define-syntax define/memo
  (syntax-rules (: →)
    [(define/memo (f [x : τ] ...) : σ e ...)
     (define f : (τ ... → σ)
       (let ([m : (HashTable (List τ ...) σ) (make-hash)])
         (λ ([x : τ] ...) : σ
            (hash-ref! m (list x ...) (λ () : σ e ...)))))]
    [(define/memo (f x ...) e ...)
     (define f
       (let ([m (make-hash)])
         (λ (x ...) (hash-ref! m (list x ...) (λ () e ...)))))]))

;; Define type `t` along with predicate `t?`
(define-syntax (define-type/pred stx)
  (syntax-case stx ()
    [(_ τ e) (with-syntax ([τ? (format-id #'τ "~a?" #'τ)])
               #'(begin (define-type τ e)
                        (define-predicate τ? τ)))]))

;; define data-type hierarchy
(define-syntax-rule (define-data τ σ ...)
  (define-data′ τ (σ ...) ()))
(define-syntax (define-data′ stx)
  (syntax-case stx (subset: struct)
    [(_ τ () (σ ...)) #'(define-type/pred τ (U σ ...))]
    [(_ τ ((subset: τ′ clauses′ ...) clauses ...) (σ ...))
     #'(begin (define-data′ τ′ (clauses′ ...) ())
              (define-data′ τ (clauses ...) (τ′ σ ...)))]
    [(_ τ ((struct k f ...) clauses ...) (σ ...))
     #'(begin (struct k (f ...) #:transparent)
              (define-data′ τ (clauses ...) (k σ ...)))]
    [(_ τ (τ₁ clauses ...) (σ ...))
     #'(define-data′ τ (clauses ...) (τ₁ σ ...))]))

(define-syntax-rule (match? v p ...) (match v [p #t] ... [_ #f]))
(define-syntax-rule (match-λ? p ...) (match-lambda [p #t] ... [_ #f]))

;; non-deterministic match. The types is to make it less awkard in pattern matching
(define-syntax match/nd:
  (syntax-rules (→)
    [(_ (α → β) v [p e ...] ...)
     (let ([x v]
           [f : (α → (U β (Setof β)))
              (match-lambda [p e ...] ... [x (error "match/nd unmatched: " x)])])
       (if (set? x)
           (for/fold ([acc : (Setof β) ∅]) ([xᵢ x])
             (define y (f xᵢ))
             (if (set? y) (set-union acc y) (set-add acc y)))
           (f x)))]))

;; define the same type for multiple identifiers
(define-syntax (:* stx)
  (syntax-parse stx
    #:literals (:)
    [(_ x:id ... : τ ...)
     #'(begin (: x : τ ...) ...)]))

(define-syntax-rule (define** [id v] ...) (define-values (id ...) (values v ...)))

;; Abbreviations
(define ∅ : (Setof Nothing) (set))
(define-type Map HashTable)
(define-type (MMap X Y) (Map X (Setof Y)))
(define-type (NeListof X) (Pairof X (Listof X)))

;; evaluate an expression within given #seconds
;; return singleton list of value, or #f on timeout
(define-syntax-rule (within-time: τ n e ...)
  (let ([c : (Channelof (U #f (List τ))) (make-channel)])
    (define t₁ (thread (λ () (channel-put c (list (begin e ...))))))
    (define t₂ (thread (λ () (sleep n) (channel-put c #f))))
    (match (channel-get c)
      [#f  (kill-thread t₁) #f]
      [ans (kill-thread t₂) ans])))

(: mmap-join! : (∀ (X Y) ((MMap X Y) X Y → Void)))
(define (mmap-join! m x y)
  (hash-update! m x (λ ([s : (Setof Y)]) (set-add s y)) (λ () ∅)))

(: mmap-join : (∀ (X Y) ((MMap X Y) X Y → (MMap X Y))))
(define (mmap-join m x y)
  (hash-update m x (λ ([s : (Setof Y)]) (set-add s y)) (λ () ∅)))

;; Define set with shortened syntax for (imperative) adding and membership testing
(define-syntax (define-set stx)
  (syntax-case stx (:)
    [(_ s : τ)
     (with-syntax ([s-has? (format-id #'s "~a-has?" #'s)]
                   [s-add! (format-id #'s "~a-add!" #'s)])
       #'(begin (define s : (Setof τ) ∅)
                (define (s-has? [x : τ]) : Boolean (set-member? s x))
                (define (s-add! [x : (U τ (Setof τ))])
                  (set! s (cond [(set? x) (set-union s x)]
                                [else (set-add s x)])))))]))

(: set-partition : (∀ (X) (X → Boolean) (Setof X) → (Values (Setof X) (Setof X))))
(define (set-partition p xs)
  (for/fold ([pass : (Setof X) ∅] [fail : (Setof X) ∅]) ([x xs])
    (if (p x)
        (values (set-add pass x) fail)
        (values pass (set-add fail x)))))

(define-syntax-rule (inc! x) (set! x (+ 1 x)))

;;;;; Pretty printing stuff

(: sym-sub : Symbol → Symbol)
(define (sym-sub x)
  (string->symbol
   (list->string
    (for/list : (Listof Char) ([c (in-string (symbol->string x))])
      (case c
        [(#\0) #\₀] [(#\1) #\₁] [(#\2) #\₂] [(#\3) #\₃] [(#\4) #\₄]
        [(#\5) #\₅] [(#\6) #\₆] [(#\7) #\₇] [(#\8) #\₈] [(#\9) #\₉]
        [else c])))))

(: vars-not-in : Integer (Listof Symbol) → (Listof Symbol))
(define vars-not-in
  (let* ([pool '(x y z u v w a b c)]
         [N (length pool)])
    (λ (n t)
      (map sym-sub (variables-not-in t (if (<= n N) (take pool n) (make-list n 'x1)))))))

(: pretty : Any → String)
(define (pretty x)
  (parameterize ([pretty-print-columns 80])
    (string-trim (with-output-to-string (λ () (pretty-display x))))))

(: n-sub : Integer → String)
(define (n-sub n)
  (cond
   [(< n 0) (format "₋~a" (n-sub (- n)))]
   [(<= 0 n 9) (substring "₀₁₂₃₄₅₆₇₈₉" n (+ n 1))]
   [else (string-append (n-sub (quotient n 10)) (n-sub (remainder n 10)))]))

(: fresh-int! : → Integer)
(define fresh-int!
  (let ([i 0])
    (λ () (begin0 i (set! i (+ 1 i))))))

(define (todo x) (error 'TODO "~a" x))
