#lang typed/racket/base
(require racket/set racket/match racket/list racket/pretty racket/string racket/port
         racket/function)
(require (for-syntax racket/base racket/syntax syntax/parse))
(provide (all-defined-out)) ; TODO
(require/typed
 redex/reduction-semantics
 [variables-not-in (Any Any → (Listof Symbol))])

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;; Customized definitions
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define-syntax-rule (define** [id v] ...) (define-values (id ...) (values v ...)))

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

;; define the same type for multiple identifiers
(define-syntax (:* stx)
  (syntax-parse stx
    #:literals (:)
    [(_ x:id ... : τ ...)
     #'(begin (: x : τ ...) ...)]))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;; Non-determinism
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

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
         [else (f x)]))]
    [(_ #:tag tag (α → β) v [p e ...] ...)
     (match/nd: (α → β) v [p e ...] ... [x (error 'tag "unmatched: ~a" x)])]))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;; List
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(: unzip-by (∀ (A X Y) (A → X) (A → Y) (Listof A) → (Values (Listof X) (Listof Y))))
(define (unzip-by f g l)
  (for/lists ([xs : (Listof X)] [ys : (Listof Y)]) ([a : A l])
    (values (f a) (g a))))

(: unzip (∀ (X Y) (Listof (Pairof X Y)) → (Values (Listof X) (Listof Y))))
(define (unzip l)
  (unzip-by (inst car X Y) (inst cdr X Y) l))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;; Set
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define ∅ : (Setof Nothing) (set))
(define ∪ set-union)
(define ∩ set-intersect)
(define ∋ set-member?)
(define →∅ : (→ (Setof Nothing)) (λ () ∅))
(: ∈ : (∀ (X) X (Setof X) → Boolean))
(define (∈ x xs) (∋ xs x))
(define ⊆ subset?)
(define -- set-subtract)

(: set-add-list : (∀ (A) (Setof A) (Listof A) → (Setof A)))
;; Add each element in given list to set
(define (set-add-list xs x-list)
  (for/fold ([xs* : (Setof A) xs]) ([x x-list])
    (set-add xs* x)))

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
;; Partition set members into those that satisfy the predicate and the rest
(define (set-partition p xs)
  (for/fold ([pass : (Setof X) ∅] [fail : (Setof X) ∅]) ([x xs])
    (if (p x)
        (values (set-add pass x) fail)
        (values pass (set-add fail x)))))

(define-syntax for/union
  (syntax-rules (: Setof)
    [(_ : (Setof τ) (for-clauses ...) body ...)
     (for/fold ([acc : (Setof τ) ∅]) (for-clauses ...)
       (set-union acc (begin body ...)))]
    [(_ (for-clauses ...) body ...)
     (for/fold ([acc ∅]) (for-clauses ...)
       (set-union acc (begin body ...)))]))

;(: collect (∀ (X) (Option X) * → (U X (Setof X))))
;; Collect all non-#f value into set,
;; optionally unpack set of size 1
(define-syntax collect
  (syntax-rules ()
    [(_) ∅]
    [(_ x z ...)
     (let ([x* x]
           [z* (collect z ...)])
       (cond [(set? x*)
              (cond [(set? z*) (∪ x* z*)]
                    [else (set-add x* z*)])]
             [x*
              (cond [(set? z*) (if (set-empty? z*) x* (set-add z* x*))]
                    [else {set z* x*}])]
             [else z*]))]))

(: set->predicate (∀ (X) (Setof X) → (X → Boolean)))
;; Convert set to predicate
(define ((set->predicate xs) x) (∋ xs x))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;; Multi-map
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define-type Map HashTable)
(define-type (MMap X Y) (Map X (Setof Y)))
(define-type (NeListof X) (Pairof X (Listof X)))
(define-type (ΔMap X Y) (Listof (Pairof X Y)))

;; Return the domain of a finite function represented as a hashtable
(: dom : (∀ (X Y) (Map X Y) → (Setof X)))
(define (dom f)
  (list->set (hash-keys f)))

(: ⊔ : (∀ (X Y) (MMap X Y) X Y → (MMap X Y)))
;; m ⊔ [x ↦ {y}]
(define (⊔ m x y)
  (hash-update m x (λ ([ys : (Setof Y)]) (set-add ys y)) →∅))

(: ⊔! : (∀ (X Y) ((MMap X Y) X Y → Void)))
;; mutate `m` to `m ⊔ [x ↦ {y}]`
(define (⊔! m x y)
  (hash-update! m x (λ ([s : (Setof Y)]) (set-add s y)) →∅))

(: ⊔* : (∀ (X Y) (MMap X Y) X (Setof Y) → (MMap X Y)))
;; m ⊔ [x ↦ ys]
(define (⊔* m x ys)
  (hash-update m x (λ ([s : (Setof Y)]) (∪ s ys)) →∅))

(: ⊔!* : (∀ (X Y) (MMap X Y) X (Setof Y) → Void))
;; mutate `m` to `m ⊔ [x ↦ ys]`
(define (⊔!* m x ys)
  (hash-update! m x (λ ([s : (Setof Y)]) (∪ s ys)) →∅))

(: ⊔/m : (∀ (X Y) (MMap X Y) (MMap X Y) → (MMap X Y)))
(define (⊔/m m₁ m₂)
  (for/fold ([m : (MMap X Y) m₁]) ([(x ys) (in-hash m₂)])
    (⊔* m x ys)))

(: Δ+ : (∀ (X Y) (ΔMap X Y) (MMap X Y) → (Values (MMap X Y) Boolean)))
;; Apply map delta to map
(define (Δ+ Δ m)
  (for/fold ([m : (MMap X Y) m] [δ? : Boolean #f]) ([δ Δ])
    (match-define (cons k v) δ)
    (values (⊔ m k v)
            (or δ? (not (∋ (hash-ref m k →∅) v))))))

(: mmap-subtract : (∀ (X Y) (MMap X Y) (MMap X Y) → (MMap X Y)))
;; Compute bindings in `m₁` not in `m₀`
(define (mmap-subtract m₁ m₀)
  (for/fold ([acc : (MMap X Y) (hash)]) ([(k v) (in-hash m₁)])
    (define δv (set-subtract v (hash-ref m₀ k →∅)))
    (cond [(set-empty? δv) acc]
          [else (hash-set acc k δv)])))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;; Pretty printing
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(: sym-sub : Symbol → Symbol)
;; Make all digits in symbol subscripts
(define (sym-sub x)
  (string->symbol
   (list->string
    (for/list ([c (in-string (symbol->string x))])
      (case c
        [(#\0) #\₀] [(#\1) #\₁] [(#\2) #\₂] [(#\3) #\₃] [(#\4) #\₄]
        [(#\5) #\₅] [(#\6) #\₆] [(#\7) #\₇] [(#\8) #\₈] [(#\9) #\₉]
        [else c])))))

(: pretty : Any → String)
;; Pretty print given object
(define (pretty x)
  (parameterize ([pretty-print-columns 80])
    (string-trim (with-output-to-string (λ () (pretty-display x))))))

(: n-sub : Integer → String)
;; Return number as subscript string
(define (n-sub n)
  (cond
   [(< n 0) (format "₋~a" (n-sub (- n)))]
   [(<= n 9) (substring "₀₁₂₃₄₅₆₇₈₉" n (+ n 1))]
   [else
    (define-values (q r) (quotient/remainder n 10))
    (string-append (n-sub q) (n-sub r))]))

(: unique-name (∀ (X) (Symbol → (X → Symbol))))
;; Return function that computes unique name with given prefix for each object.
;; No guarantee for consistency across different executions.
(define (unique-name prefix)
  (let ([m : (Map X Symbol) (make-hash)])
    (λ ([x : X])
      (hash-ref! m x (λ () (string->symbol
                            (format "~a~a" prefix (n-sub (hash-count m)))))))))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;; Functions
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(: fix : (∀ (X) (X → X) X → X))
;; Compute `f`'s fixpoint starting from `x`
(define (fix f x)
  (define x* (f x))
  (if (equal? x x*) x (fix f x*)))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;; Specialized match
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define-syntax (define-datum-map stx)
  
  (define-syntax-class dtm
    #:description "restricted datum"
    (pattern (~or n:number x:id b:boolean)))
  
  (syntax-parse stx
    #:literals (: →)
    [(_ f:id : (α → β) [d:dtm v] ... #:else k)
     #'(define f
         (let ([m : (HashTable α β) (make-hasheq)])
           (hash-set! m 'd v) ...
           (λ ([x : α]) (hash-ref m x (λ () (k x))))))]))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;; Controlled evaluation
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; evaluate an expression within given #seconds
;; return singleton list of value, or #f on timeout
(define-syntax-rule (within-time: τ n e ...)
  (let ([c : (Channelof (U #f (List τ))) (make-channel)])
    (define t₁ (thread (λ () (channel-put c (list (begin e ...))))))
    (define t₂ (thread (λ () (sleep n) (channel-put c #f))))
    (match (channel-get c)
      [#f  (kill-thread t₁) #f]
      [ans (kill-thread t₂) ans])))

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


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;; Debuggings
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define debugs : (Parameterof (Setof Symbol)) (make-parameter ∅))
(define-syntax-rule (with-debug t e ...)
  (parameterize ([debugs (set-add (debugs) t)]) e ...))
(: dbg : Symbol String Any * → Void)
(define (dbg t fmt . xs)
  (when (∋ (debugs) t)
    (apply printf fmt xs)))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;; Symbols
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define next-neg!
  (let ([n : Negative-Integer -1])
    (λ () : Negative-Integer
      (begin0 n (set! n (- n 1))))))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;; abbreviations
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define-type Sexps (Listof Sexp))
(define (todo x) (error 'TODO "~a" x))
