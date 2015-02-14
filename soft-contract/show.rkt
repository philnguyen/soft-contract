#lang typed/racket/base
(require racket/match racket/list racket/set racket/function
         "utils.rkt" "lang.rkt" "runtime.rkt")

(provide (all-defined-out))

(define abstract-V? (make-parameter #t))

(: show-Ans : (case→ [.Ans → (Pairof Any Any)] [.σ .A → (Pairof Any Any)]))
(define show-Ans
  (case-lambda
    [(σ A) (cons (show-E σ A) (show-σ σ))]
    [(Ans) (show-Ans (car Ans) (cdr Ans))]))

(: show-A : .σ .A → Any)
(define (show-A σ A)
  (match A
    [(.blm l+ lo V C) `(blame ,l+ ,lo ,(show-V σ V) ,(show-V σ C))]
    [(? .V? V) (show-V σ V)]))

(: show-V : (case→ [.σ .V → Any]
                   [.σ (Listof .V) → (Listof Any)]))
(define (show-V σ V)
  (match V
    [(.L i) (if (abstract-V?) (show-V σ (σ@ σ i)) (format "L~a" (n-sub i)))]
    [(.// U C*) (if (.•? U)
                    `(• ,@(for/list : (Listof Any) ([C C*]) (show-V σ C)))
                    (show-U σ U))]
    [(.X/V x) x]
    [(.μ/V x V*) `(μ (,x) ,(for/list : (Listof Any) ([V V*]) (show-V σ V)))]
    [(? list? V*) (map (curry show-V σ) V*)]))

(: show-U : .σ .U → Any)
(define (show-U σ U)
  (match U
    [(.b b) (show-b b)]
    ['• '•]
    #;[(or (? .Ar?) (.o) (? .λ↓?)) 'function]
    [(? .o? o) (name o)]
    [(.λ↓ f _) (show-e σ f)]
    [(.Ar C V _) `(,(show-V σ C) ◃ ,(show-V σ V))]
    [(.St '¬/c (list (.// (.λ↓ (.λ 1 (.@ '= (list (.x 0) e) _) _) _) _))) `(≠/c ,(show-e σ e))]
    [(.St 'empty (list)) 'empty]
    [(.St (and n (or 'and/c 'or/c)) V*) `(,n ,@(show-V σ V*))]
    [(.St '¬/c V*) `(not/c ,@(show-V σ V*))]
    [(.St t V*) `(,t ,@(show-V σ V*))]
    [(.Λ/C Cx D v?) `(,@(show-V σ Cx) ,(if v? '↦* '↦) ,(show-E σ D))]
    [(.St/C t V*) `(,(string->symbol (format "~a/c" t)) ,@(show-V σ V*))]
    [(.μ/C x V) `(μ/C (,x) ,(show-V σ V))]
    [(.X/C x) x]
    [(.Case m) `(case-λ ,@(show-cases σ m))]))

(: show-cases : .σ (Map (Listof .V) .L) → (Listof Any))
(define (show-cases σ m)
  (define show (curry show-V σ))
  (for/list ([(k* v) (in-hash m)])
    `(,(map show k*) ,(show v))))

(: show-ρ : .σ .ρ → Any)
(define (show-ρ σ ρ)
  (match-let ([(.ρ m l) ρ])
    (for/list : (Listof Any) ([x (in-hash-keys m)])
      (cond
        [(symbol? x) `(,x ↦ ,(show-V σ (hash-ref m x)))]
        [(integer? x) `(,(format "sd~a" (n-sub (- l x 1))) ↦ ,(show-V σ (hash-ref m x)))]))))

(: show-E : .σ .E → Any)
(define (show-E σ E)
  (match E
    [(.L i) (string->symbol (format "L~a" (n-sub i)))]
    [(? .A? A) (show-A σ A)]
    [(.↓ e ρ) (show-e σ e)]
    [(.FC C V l) `(FC ,l ,(show-E σ C) ,(show-E σ V))]
    [(.Mon C E l³) `(Mon ,l³ ,(show-E σ C) ,(show-E σ E))]
    [(.Assume V C) `(Asm ,(show-E σ V) ,(show-E σ C))]))

(: show-e : .σ .e → Any)
(define (show-e σ e)
  (let go ([ctx : (Listof Symbol) '()] [e e])
    (match e
      ; syntactic sugar
      [(.λ 1 (.@ '= (list (.x 0) e′) _) _) `(=/c ,(go ctx e′))]
      [(.λ 1 (.@ 'equal? (list (.x 0) e′) _) _) `(≡/c ,(go ctx e′))]
      [(.λ 1 (.@ '> (list (.x 0) e′) _) _) `(>/c ,(go ctx e′))]
      [(.λ 1 (.@ '< (list (.x 0) e′) _) _) `(</c ,(go ctx e′))]
      [(.λ 1 (.@ '>= (list (.x 0) e′) _) _) `(≥/c ,(go ctx e′))]
      [(.λ 1 (.@ '<= (list (.x 0) e′) _) _) `(≤/c ,(go ctx e′))]
      [(.λ 1 (.@ (? closed? f) (list (.x 0)) _) _) (go '() f)]
      [(.λ 1 (.@ 'arity-includes? (list (.x 0) (.b x)) _) #f) `(arity-includes/c ,x)]
      [(.λ 1 (.@ 'arity=? (list (.x 0) (.b x)) _) #f) `(arity=/c ,x)]
      [(.λ 1 (.@ 'arity>=? (list (.x 0) (.b x)) _) #f) `(arity≥/c ,x)]
      #;[(.@ (.st-mk 'or/c _) (list (.@ (.st-mk '¬/c _) (list c) _) d) _)
       `(⇒/c ,(go ctx c) ,(go ctx d))]
      [(.λ 1 (.b (not #f)) #f) 'any/c]
      [(.λ 1 (.b #f) #f) 'none/c]
      [(.@ (.st-mk 'empty 0) (list) _) 'empty]
      [(.@ (.λ 1 (.x 0) _) (list e) _) (go ctx e)]
      [(.@ (.λ 1 (.if (.x 0) (.x 0) b) #f) (list a) _)
       (match* ((go ctx a) (go (append (vars-not-in 1 ctx) ctx) b))
         [(`(or ,l ...) `(or ,r ...)) `(or ,@l ,@r)]
         [(`(or ,l ...) r) `(or ,@l ,r)]
         [(l `(or ,r ...)) `(or ,l ,@r)]
         [(l r) `(or ,l ,r)])]
      [(.@ (.st-mk (and n (or 'and/c 'or/c '¬/c)) _) c* _) `(,n ,@(map (curry go ctx) c*))]
      ;; Direct case-λ application
      [(.@ (.•ₗ (and n (? (λ ([n : Integer]) (match? (σ@ σ n) (.// (? .Case?) _)))))) (list e) _)
       (match-define (.// (.Case m) _) (σ@ σ n))
       `(case ,(go ctx e) ,@(show-cases σ m))]
      ;; Direct λ application
      [(.@ (.λ n e #f) ex _)
       (define x* (vars-not-in n ctx))
       `(let ,(for/list : (Listof Any) ([x (reverse x*)] [ei ex])
                `(,x ,(go ctx ei)))
         ,(go (append x* ctx) e))]
      [(.@ (.•ₗ (and n (? (λ ([n : Integer]) (match? (σ@ σ n) (.// (.λ↓ (.λ _ _ #f) _) _)))))) es _)
       (match-let ([(.// (.λ↓ (.λ k e #f) ρ) _) (σ@ σ n)])
         (cond
          ;; Inline if all arguments are simple or all parameters appear at most once.
          ;; TODO: can do better, inline each argument?
          [(or (andmap inlinable? es)
               (for/and : Boolean ([i : Integer (in-range k)]) (<= (count-xs e i) 1)))
           (go ctx (for/fold ([e e]) ([i (in-range (- k 1) -1 -1)] [eᵢ es])
                     (e/ e i eᵢ)))]
          ;; Default to `let`
          [else
           (define xs (vars-not-in k ctx))
           `(let ,(for/list : (Listof Any) ([xᵢ (reverse xs)] [eᵢ es])
                    `(,xᵢ ,(go ctx eᵢ)))
             ,(go xs e))]))]
      ;; Fix confusing ill-typed (though correct) value at function position
      ;; as a reminiscent of `havoc`
      [(.@ (.•ₗ (? (λ ([n : Integer])
                     (match? (σ@ σ n) (.// (.b (? number?)) _)))))
           (list x) (or '† '☠))
       (go ctx x)]
      [(.if (and e (.•ₗ α)) e₁ e₂)
       (match (σ@ σ α)
         [(.// (.b #f) _) (go ctx e₂)]
         [(.// (not (? .•?)) _) (go ctx e₁)]
         [_ `(if ,(go ctx e) ,(go ctx e₁) ,(go ctx e₂))])]
      [(.if a b (.b #f))
       (match* ((go ctx a) (go ctx b))
         [(`(and ,l ...) `(and ,r ...)) `(and ,@l ,@r)]
         [(`(and ,l ...) r) `(and ,@l ,r)]
         [(l `(and ,r ...)) `(and ,l ,@r)]
         [(l r) `(and ,l ,r)])]
      [(.if a b (.b #t)) `(implies ,(go ctx a) ,(go ctx b))]
      [(.λ n e v?)
       (define x* (vars-not-in n ctx))
       `(,(if v? 'λ* 'λ) ,(reverse x*) ,(go (append x* ctx) e))]
      [(.•ₗ α) (syn σ α)]
      ['• '•]
      [(.b b) (show-b b)]
      [(.st-mk t _) t]
      [(.st-ac 'cons _ 0) 'car]
      [(.st-ac 'cons _ 1) 'cdr]
      [(.st-ac t _ i) (string->symbol (format "~a@~a" t i))]
      [(.st-p t _) (string->symbol (format "~a?" t))]
      [(? .o? o) (name o)]
      [(.x i) (ctx-ref ctx i)]
      [(.ref x _ _) x]
      [(.@ f xs _) `(,(go ctx f) ,@(map (curry go ctx) xs))]
      [(.@-havoc x) `(apply ,(go ctx x) •)]
      #;[(.apply f xs _) `(@ ,(go ctx f) ,(go ctx xs))]
      [(.if i t e) `(if ,(go ctx i) ,(go ctx t) ,(go ctx e))]
      [(.amb e*) `(amb ,@(for/list : (Listof Any) ([e e*]) (go ctx e)))]
      [(.μ/c x c) `(μ/c (,x) ,(go ctx c))]
      [(.λ/c c d v?) `(,@(map (curry go ctx) c) ,(if v? '↦* '↦) ,(go ctx d))]
      [(.x/c x) x]
      [(.struct/c t cs) `(,(string->symbol (format "~a/c" t)) ,@(map (curry go ctx) cs))])))

(define (inlinable? [e : .e]) : Boolean
  (or (.x? e) (.ref? e) (.prim? e)))

(: show-b : (U Number String Boolean Symbol) → Any)
(define (show-b x)
  (cond
   [(string? x) (format "\"~a\"" x)]
   [(symbol? x) `(quote ,x)]
   [(and (real? x) (inexact? x))
    (define s (number->string x))
    (substring s 0 (min (string-length s) 5))]
   [else x]))

(: show-σ : .σ → (Listof Any))
(define (show-σ σ)
  (match-define (.σ m _) σ)
  (parameterize ([abstract-V? #f])
    (for/list : (Listof Any) ([(i v) (in-hash m)])
      `(,(format "L~a" (n-sub i)) ↦ ,(show-E σ v)))))

(: ctx-ref : (Listof Symbol) Integer → Symbol)
(define (ctx-ref xs i)
  (let go ([xs xs] [i i])
    (match* (xs i)
      [('() _) (string->symbol (format "…~a" (n-sub i)))]
      [((cons x _) 0) x]
      [((cons _ xr) i) (go xr (- i 1))])))

(: show-ce : .p .σ → (Listof Any))
(define (show-ce p σ)
  (match-define (.p (.m* order ms) _ e†) p)
  #;(log-debug "σ:~n~ae†:~n~a~n" σ e†)
  (list
   (for*/list : (Listof (Listof Any))
              ([m-name order]
               [m (in-value (hash-ref ms m-name))]
               [m-order (in-value (.m-order m))]
               [defs (in-value (.m-defs m))]
               [res
                (in-value
                 (for*/list : (Listof Any)
                            ([x-name m-order]
                             [v (in-value (car (hash-ref defs x-name)))]
                             #;[_ (in-value (log-debug "Value is: ~a~n" v))]
                             #:when (.•ₗ? v))
                   `(,x-name : ,(syn σ (.•ₗ-l v)))))]
               #:unless (empty? res))
     `(,m-name : ,@res))
   (show-e σ e†)))

(: syn : .σ Integer → Any)
(define (syn σ α)
  (match-define (.σ m _) σ)
  (match (hash-ref m α #f)
    [(? .V? V) (show-V σ (σ@ σ α))]
    [else #f #|ok?|# #;(format "•~a" (n-sub α))]))
