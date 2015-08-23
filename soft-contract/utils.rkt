#lang typed/racket/base
(require racket/set racket/match racket/list racket/pretty racket/string racket/port
         racket/function)
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
     (let ()
       (define x v)
       (define f : (α → (U β (Setof β)))
         (match-lambda [p e ...] ... [x (error 'match/nd "unmatched: ~a" x)]))
       (cond
         [(set? x) (for/fold ([acc : (Setof β) ∅]) ([xᵢ x])
                     (define y (f xᵢ))
                     (if (set? y) (set-union acc y) (set-add acc y)))]
         [else (f x)]))]))

;; define the same type for multiple identifiers
(define-syntax (:* stx)
  (syntax-parse stx
    #:literals (:)
    [(_ x:id ... : τ ...)
     #'(begin (: x : τ ...) ...)]))

(define-syntax-rule (define** [id v] ...) (define-values (id ...) (values v ...)))

;; Abbreviations
(define ∅ : (Setof Nothing) (set))
(define ∪ set-union)
(define ∩ set-intersect)
(define ∋ set-member?)
(: ∈ : (∀ (X) X (Setof X) → Boolean))
(define (∈ x xs) (∋ xs x))
(define ⊆ subset?)
(define -- set-subtract)
(define-type Map HashTable)
(define-type (MMap X Y) (Map X (Setof Y)))
(define-type (NeListof X) (Pairof X (Listof X)))

(: set-add-list : (∀ (A) (Setof A) (Listof A) → (Setof A)))
;; Add each element in given list to set
(define (set-add-list xs x-list)
  (for/fold ([xs* : (Setof A) xs]) ([x x-list])
    (set-add xs* x)))

;; evaluate an expression within given #seconds
;; return singleton list of value, or #f on timeout
(define-syntax-rule (within-time: τ n e ...)
  (let ([c : (Channelof (U #f (List τ))) (make-channel)])
    (define t₁ (thread (λ () (channel-put c (list (begin e ...))))))
    (define t₂ (thread (λ () (sleep n) (channel-put c #f))))
    (match (channel-get c)
      [#f  (kill-thread t₁) #f]
      [ans (kill-thread t₂) ans])))

;; Return the domain of a finite function represented as a hashtable
(: dom : (∀ (X Y) (Map X Y) → (Setof X)))
(define (dom f)
  (list->set (hash-keys f)))

(: ⊔ : (∀ (X Y) (MMap X Y) X Y → (MMap X Y)))
;; m ⊔ [x ↦ {y}]
(define (⊔ m x y)
  (hash-update m x (λ ([ys : (Setof Y)]) (set-add ys y)) (λ () ∅)))

(: ⊔! : (∀ (X Y) ((MMap X Y) X Y → Void)))
;; mutate `m` to `m ⊔ [x ↦ {y}]`
(define (⊔! m x y)
  (hash-update! m x (λ ([s : (Setof Y)]) (set-add s y)) (λ () ∅)))

(: ⊔* : (∀ (X Y) (MMap X Y) X (Setof Y) → (MMap X Y)))
;; m ⊔ [x ↦ ys]
(define (⊔* m x ys)
  (hash-update m x (λ ([s : (Setof Y)]) (∪ s ys)) (λ () ∅)))

(: ⊔!* : (∀ (X Y) (MMap X Y) X (Setof Y) → Void))
;; mutate `m` to `m ⊔ [x ↦ ys]`
(define (⊔!* m x ys)
  (hash-update! m x (λ ([s : (Setof Y)]) (∪ s ys)) (λ () ∅)))

(: ⊔/m : (∀ (X Y) (MMap X Y) (MMap X Y) → (MMap X Y)))
(define (⊔/m m₁ m₂)
  (for/fold ([m : (MMap X Y) m₁]) ([(x ys) (in-hash m₂)])
    (⊔* m x ys)))

;; Define set with shortened syntax for (imperative) adding and membership testing
(define-syntax (define-set stx)
  (syntax-case stx (:)
    [(_ s : τ)
     (with-syntax ([s-has? (format-id #'s "~a-has?" #'s)]
                   [s-add! (format-id #'s "~a-add!" #'s)]
                   [s-add*! (format-id #'s "~a-add*!" #'s)]
                   [s-union! (format-id #'s "~a-union!" #'s)])
       #'(begin (define s : (Setof τ) ∅)
                (define (s-has? [x : τ]) : Boolean (∋ s x))
                (define (s-add! [x : τ]) (set! s (set-add s x)))
                (define (s-add*! [xs : (Listof τ)]) (set! s (∪ s (list->set xs))))
                (define (s-union! [xs : (Setof τ)]) (set! s (∪ s xs)))))]))

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
    (for/list ([c (in-string (symbol->string x))])
      (case c
        [(#\0) #\₀] [(#\1) #\₁] [(#\2) #\₂] [(#\3) #\₃] [(#\4) #\₄]
        [(#\5) #\₅] [(#\6) #\₆] [(#\7) #\₇] [(#\8) #\₈] [(#\9) #\₉]
        [else c])))))

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

(define (todo x) (error 'TODO "~a" x))

(define-syntax for/union
  (syntax-rules (: Setof)
    [(_ : (Setof τ) (for-clauses ...) body ...)
     (for/fold ([acc : (Setof τ) ∅]) (for-clauses ...)
       (set-union acc (begin body ...)))]
    [(_ (for-clauses ...) body ...)
     (for/fold ([acc ∅]) (for-clauses ...)
       (set-union acc (begin body ...)))]))

;; Application with implicit #f for failure for expressions marked with (!)
;; e.g. (@? cons (! #f) 2) --> #f
;; e.g. (@? cons #f 2) --> ⟨1, 2⟩
(define-syntax @?
  (syntax-rules (!)
    [(_ f e ...) (@?* f (e ...) ())]))
(define-syntax @?*
  (syntax-rules (!)
    [(_ f ()             (x ...)) (f x ...)]
    [(_ f ((! e₁) e ...) (x ...))
     (let ([x₁ e₁])
       (if x₁ (@?* f (e ...) (x ... x₁)) #f))]
    [(_ f (e₁     e ...) (x ...))
     (let ([x₁ e₁])
       (@?* f (e ...) (x ... x₁)))]))
