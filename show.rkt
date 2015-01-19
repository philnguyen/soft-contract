#lang typed/racket/base
(require racket/match racket/list racket/set racket/function
         "utils.rkt" "lang.rkt" "runtime.rkt")

(provide (all-defined-out))

(define abstract-V? (make-parameter #t))

(: show-Ans : (case→ [.Ans → (Pairof Sexp Sexp)] [.σ .A → (Pairof Sexp Sexp)]))
(define show-Ans
  (case-lambda
    [(σ A) (cons (show-E σ A) (show-σ σ))]
    [(Ans) (show-Ans (car Ans) (cdr Ans))]))

(: show-A : .σ .A → Sexp)
(define (show-A σ A)
  (match A    
    [(.blm l+ lo V C) `(blame ,l+ ,lo ,(show-V σ V) ,(show-V σ C))]
    [(? .V? V) (show-V σ V)]))

(: show-V : (case→ [.σ .V → Sexp]
                   [.σ (Listof .V) → (Listof Sexp)]))
(define (show-V σ V)
  (match V
    [(.L i) (if (abstract-V?) (show-V σ (σ@ σ i)) (format "L~a" (n-sub i)))]
    [(.// U C*) (if (.•? U)
                    `(• ,@(for/list : (Listof Sexp) ([C C*]) (show-V σ C)))
                    (show-U σ U))]
    [(.X/V x) (syntax->datum x)]
    [(.μ/V x V*) `(μ (,(syntax->datum x)) ,(for/list : (Listof Sexp) ([V V*]) (show-V σ V)))]
    [(? list? V*) (map (curry show-V σ) V*)]))

(: show-U : .σ .U → Sexp)
(define (show-U σ U)
  (match U
    [(.b b) (show-b b)]
    ['• '•]
    #;[(or (? .Ar?) (.o) (? .λ↓?)) 'function]
    [(? .o? o) (name o)]
    [(.λ↓ f _) (show-e σ f)]
    [(.Ar C V _) `(,(show-V σ C) ◃ ,(show-V σ V))]
    [(.St '¬/c (list (.// (.λ↓ (.λ 1 (.@ '= (list (.x 0) e) _)) _) _))) `(≠/c ,(show-e σ e))]
    [(.St 'empty (list)) 'empty]
    [(.St (and n (or 'and/c 'or/c)) V*) `(,n ,@(show-V σ V*))]
    [(.St '¬/c V*) `(not/c ,@(show-V σ V*))]
    [(.St t V*) `(,(syntax->datum t) ,@(show-V σ V*))]
    [(.Λ/C Cx D v?) `(,@(show-V σ Cx) ,(if v? '↦* '↦) ,(show-E σ D))]
    [(.St/C t V*) `(,(string->symbol (format "~a/c" t)) ,@(show-V σ V*))]
    [(.μ/C x V) `(μ/C (,(syntax->datum x)) ,(show-V σ V))]
    [(.X/C x) (syntax->datum x)]
    [(.Case m) `(case-λ ,@(show-cases σ m))]))

(: show-cases : .σ (Map (Listof .V) .L) → (Listof Sexp))
(define (show-cases σ m)
  (define show (curry show-V σ))
  (for/list ([(k* v) (in-hash m)])
    `(,(map show k*) ,(show v))))

(: show-ρ : .σ .ρ → Sexp)
(define (show-ρ σ ρ)
  (match-let ([(.ρ m l) ρ])
    (for/list : (Listof Sexp) ([x (in-hash-keys m)])
      (cond
        [(identifier? x) `(,(syntax->datum x) ↦ ,(show-V σ (hash-ref m x)))]
        [(integer? x) `(,(format "sd~a" (n-sub (- l x 1))) ↦ ,(show-V σ (hash-ref m x)))]))))

(: show-E : .σ .E → Sexp)
(define (show-E σ E)
  (match E
    [(.L i) (string->symbol (format "L~a" (n-sub i)))]
    [(? .A? A) (show-A σ A)]
    [(.↓ e ρ) (show-e σ e)]
    [(.FC C V l) `(FC ,l ,(show-E σ C) ,(show-E σ V))]
    [(.Mon C E l³) `(Mon ,l³ ,(show-E σ C) ,(show-E σ E))]
    [(.Assume V C) `(Asm ,(show-E σ V) ,(show-E σ C))]))

(: show-e : .σ .expr → Sexp)
(define (show-e σ e)
  (let go ([ctx : (Listof Symbol) '()] [e e])
    (match e
      ; syntactic sugar
      [(.λ 1 (.@ '= (list (.x 0) e′) _)) `(=/c ,(go ctx e′))]
      [(.λ 1 (.@ 'equal? (list (.x 0) e′) _)) `(≡/c ,(go ctx e′))]
      [(.λ 1 (.@ '> (list (.x 0) e′) _)) `(>/c ,(go ctx e′))]
      [(.λ 1 (.@ '< (list (.x 0) e′) _)) `(</c ,(go ctx e′))]
      [(.λ 1 (.@ '>= (list (.x 0) e′) _)) `(≥/c ,(go ctx e′))]
      [(.λ 1 (.@ '<= (list (.x 0) e′) _)) `(≤/c ,(go ctx e′))]
      [(.λ 1 (.@ (? closed? f) (list (.x 0)) _)) (go '() f)]
      [(.λ 1 (.@ 'arity-includes? (list (.x 0) (.b x)) _)) `(arity-includes/c ,x)]
      [(.λ 1 (.@ 'arity=? (list (.x 0) (.b x)) _)) `(arity=/c ,x)]
      [(.λ 1 (.@ 'arity>=? (list (.x 0) (.b x)) _)) `(arity≥/c ,x)]
      #;[(.@ (.st-mk 'or/c _) (list (.@ (.st-mk '¬/c _) (list c) _) d) _)
       `(⇒/c ,(go ctx c) ,(go ctx d))]
      [(.λ 1 (.b (not #f))) 'any/c]
      [(.λ 1 (.b #f)) 'none/c]
      [(.@ (.st-mk (?id #'null) 0) (list) _) 'null]
      [(.@ (.λ 1 (.x 0)) (list e) _) (go ctx e)]
      [(.@ (.λ 1 (.if (.x 0) (.x 0) b)) (list a) _)
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
      [(.@ (.λ n e) ex _)
       (define x* (vars-not-in n ctx))
       `(let ,(for/list : (Listof Sexp) ([x (reverse x*)] [ei ex])
                `(,x ,(go ctx ei)))
         ,(go (append x* ctx) e))]
      [(.@ (.•ₗ (and n (? (λ ([n : Integer]) (match? (σ@ σ n) (.// (.λ↓ (.λ _ _) _) _)))))) es _)
       (match-let ([(.// (.λ↓ (.λ k e) ρ) _) (σ@ σ n)])
         (cond
          ;; Inline if all arguments are simple. TODO: can do better, for each argument?
          [(for/and : Boolean ([eᵢ es]) (or (.x? eᵢ) (.ref? eᵢ) (.v? eᵢ)))
           (go ctx (for/fold ([e e]) ([i (in-range (- k 1) -1 -1)] [eᵢ es])
                     (e/ e i eᵢ)))]
          ;; Default to `let`
          [else
           (define xs (vars-not-in k ctx))
           `(let ,(for/list : (Listof Sexp) ([xᵢ (reverse xs)] [eᵢ es])
                    `(,xᵢ ,(go ctx eᵢ)))
             ,(go xs e))]))]
      [(.if (and e (.•ₗ α)) e₁ e₂)
       (match (σ@ σ α)
         [(.// (.b #f) _) (go ctx e₂)]
         [(.// (not (? .•?)) _) (go ctx e₁)]
         [_ `(if ,(go ctx e) ,(go ctx e₁) ,(go ctx e₂))])]
      [(.if a b (.b #f))
       (match* ((go ctx a) (go ctx b))
         [(`(and ,l ...) `(and ,r ...)) `(and ,@l ,@r)]
         [(`(and ,l ...) r) `(and ,@l ,(cast r Sexp))]
         [(l `(and ,r ...)) `(and ,l ,@(cast r Sexp))]
         [(l r) `(and ,(cast l Sexp) ,(cast r Sexp))])]
      [(.if a b (.b #t)) `(implies ,(go ctx a) ,(go ctx b))]
      
      
      [(.λ n e)
       (define x* (vars-not-in n ctx))
       `(λ ,(reverse x*) ,(go (append x* ctx) e))]
      [(.•ₗ α) (syn σ α)]
      [(.b b) (show-b b)]
      [(.st-mk t _) (syntax->datum t)]
      [(.st-ac (?id cons-id) _ 0) 'car]
      [(.st-ac (?id cons-id) _ 1) 'cdr]
      [(.st-ac t _ i) (string->symbol (format "~a@~a" (syntax->datum t) i))]
      [(.st-p t _) (string->symbol (format "~a?" (syntax->datum t)))]
      [(? .o? o) (name o)]
      [(.x i) (ctx-ref ctx i)]
      [(.ref x _ _) (syntax->datum x)]
      [(.@ f xs _) `(,(go ctx f) ,@(map (curry go ctx) xs))]
      [(.@-havoc x) `(apply ,(go ctx x) •)]
      #;[(.apply f xs _) `(@ ,(go ctx f) ,(go ctx xs))]
      [(.if i t e) `(if ,(go ctx i) ,(go ctx t) ,(go ctx e))]
      [(.amb e*) `(amb ,@(for/list : (Listof Sexp) ([e e*]) (go ctx e)))]
      [(.μ/c x c) `(μ/c (,(syntax->datum x)) ,(go ctx c))]
      [(.λ/c c d v?) `(,@(map (curry go ctx) c) ,(if v? '↦* '↦) ,(go ctx d))]
      [(.x/c x) (syntax->datum x)]
      [(.struct/c t cs) `(,(string->symbol (format "~a/c" t)) ,@(map (curry go ctx) cs))])))

(: show-b : (U Number String Boolean Symbol) → Sexp)
(define (show-b x)
  (cond
   [(string? x) (format "\"~a\"" x)]
   [(and (real? x) (inexact? x))
    (define s (number->string x))
    (substring s 0 (min (string-length s) 5))]
   [else x]))

(: show-σ : .σ → (Listof Sexp))
(define (show-σ σ)
  (match-define (.σ m _) σ)
  (parameterize ([abstract-V? #f])
    (for/list : (Listof Sexp) ([(i v) (in-hash m)])
      `(,(format "L~a" (n-sub i)) ↦ ,(show-E σ v)))))

(: ctx-ref : (Listof Symbol) Integer → Symbol)
(define (ctx-ref xs i)
  (let go ([xs xs] [i i])
    (match* (xs i)
      [('() _) (string->symbol (format "…~a" (n-sub i)))]
      [((cons x _) 0) x]
      [((cons _ xr) i) (go xr (- i 1))])))

(: show-ce : .prog .σ → Sexp)
(define (show-ce p σ)
  (match-define (.prog _ top) p)
  #;(printf "σ:~n~ae†:~n~a~n" σ e†)
  ;; TODO: ignore modules for current need
  (show-e σ top))

(: syn : .σ Integer → Sexp)
(define (syn σ α)
  (match-define (.σ m _) σ)
  (match (hash-ref m α #f)
    [(? .V? V) (show-V σ (σ@ σ α))]
    [else #f #|ok?|# #;(format "•~a" (n-sub α))]))
