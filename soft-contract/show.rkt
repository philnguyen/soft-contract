#lang typed/racket/base
(require racket/match racket/list racket/set racket/function
         "utils.rkt" "lang.rkt" "runtime.rkt")

(provide (all-defined-out))

(define-type Sexps (Listof Sexp))

(: show-Ans : -σ -A → (Pairof Sexp Sexp))
(define (show-Ans σ A)
  (cons (show-E σ A) (show-σ σ)))

(: show-A : -σ -A → Sexp)
(define (show-A σ A)
  (match A
    [(-blm l+ lo V C) `(blame ,l+ ,lo ,(show-V σ V) ,(show-V σ C))]
    [(-Ws Ws) (show-Ws σ Ws)]))

(: show-Ws : -σ (Listof -W) → (Listof Sexp))
(define (show-Ws σ Ws) (map (curry show-W σ) Ws))

(: show-W : -σ -W → Sexp)
(define (show-W σ W)
  (cons (show-V σ (-W-V W)) (show-π (-W-π W))))

(: show-Vs : -σ (Sequenceof -V) → (Listof Sexp))
(define (show-Vs σ Vs)
  (for/list : (Listof Sexp) ([V Vs]) (show-V σ V)))

(: show-V : -σ -V → Sexp)
(define (show-V σ V)
  (match V
    [(-b b) (show-b b)]
    ['• '●]
    [(? -o? o) (name o)]
    [(-λ↓ f _ _) (show-e σ f)]
    [(-Ar γ α _) `(,(show-α σ γ) ◃ ,(show-α σ α))]
    #| TODO obsolete?
    [(-st (-id 'not/c 'Λ) (list (.// (-λ↓ (-λ 1 (-@ '= (list (-x 0) e) _)) _) _))) `(≠/c ,(show-e σ e))]
    [(-st (-id t 'Λ) (list)) t]
    [(-st (-id (and n (or 'and/c 'or/c)) 'Λ) V*) `(,n ,@(show-Vs σ V*))]
    [(-st (-id 'not/c 'Λ) V*) `(not/c ,@(show-Vs σ V*))]
    |#
    [(-St t αs) `(,(-id-name t) ,@(show-αs σ αs))]
    [(-λ/C γs e ρ Γ v?) `(,@(show-αs σ γs) ,(if v? '↦* '↦) ,(show-e σ e))]
    [(-St/C t αs) `(,(string->symbol (format "~a/c" (-id-name t))) ,@(show-αs σ αs))]
    [(-μ/C x α) `(μ/C (,x) ,(show-α σ α))]
    [(-X/C α) `(X: ,(show-α σ α))]))

(: show-αs : -σ (Listof -α) → (Listof Sexp))
(define (show-αs σ αs) (map (curry show-α σ) αs))

(: show-α : -σ -α → Sexp)
(define (show-α σ α)
  (match α
    [(-α-cnc e v) `(cnc: ,(show-e σ e) ,(show-e σ v))]
    [(-α-opq e π Γ) `(cnc: ,(show-e σ e) ,(show-π π) ,(show-Γ Γ))]))

(: show-π : -π* → Sexp)
(define (show-π π)
  (cond
    [(-π@? π) `(@ ,(show-π (-π@-f π))
                  ,@(for/list : (Listof Sexp) ([x (-π@-xs π)]) (show-π x)))]
    [(-id? π) (-id-name π)]
    [π (show-e σ∅ π)]
    [else '⊘]))

(: show-Γ : -Γ → (Listof Sexp))
(define (show-Γ Γ)
  (for/list : (Listof Sexp) ([π Γ]) (show-π π)))

(: show-ρ : -σ -ρ → (Listof Sexp))
(define (show-ρ σ ρ)
  (match-define (-ρ m l) ρ)
  (for/list ([(x α) (in-hash m)])
    `(,(format "sd~a" (n-sub (- l x 1))) ↦ ,(show-α σ α))))

(: show-E : -σ -E → Sexp)
(define (show-E σ E)
  (match E
    [(? -A? A) (show-A σ A)]
    [(-↓ e _) (show-e σ e)]))

(: show-e : -σ -expr → Sexp)
(define (show-e σ e)
  (let go ([ctx : (Listof Symbol) '()] [e e])
    (match e
      ; syntactic sugar
      [(-λ 1 (-@ '= (list (-x 0) e′) _)) `(=/c ,(go ctx e′))]
      [(-λ 1 (-@ 'equal? (list (-x 0) e′) _)) `(≡/c ,(go ctx e′))]
      [(-λ 1 (-@ '> (list (-x 0) e′) _)) `(>/c ,(go ctx e′))]
      [(-λ 1 (-@ '< (list (-x 0) e′) _)) `(</c ,(go ctx e′))]
      [(-λ 1 (-@ '>= (list (-x 0) e′) _)) `(≥/c ,(go ctx e′))]
      [(-λ 1 (-@ '<= (list (-x 0) e′) _)) `(≤/c ,(go ctx e′))]
      [(-λ 1 (-@ (? closed? f) (list (-x 0)) _)) (go '() f)]
      [(-λ 1 (-@ 'arity-includes? (list (-x 0) (-b x)) _)) `(arity-includes/c ,x)]
      [(-λ 1 (-@ 'arity=? (list (-x 0) (-b x)) _)) `(arity=/c ,x)]
      [(-λ 1 (-@ 'arity>=? (list (-x 0) (-b x)) _)) `(arity≥/c ,x)]
      #;[(-@ (-st-mk 'or/c _) (list (-@ (-st-mk 'not/c _) (list c) _) d) _)
       `(⇒/c ,(go ctx c) ,(go ctx d))]
      [(-λ 1 (-b (not #f))) 'any/c]
      [(-λ 1 (-b #f)) 'none/c]
      [(-@ (-st-mk (-id 'null 'Λ) 0) (list) _) 'null]
      [(-@ (-λ 1 (-x 0)) (list e) _) (go ctx e)]
      [(-@ (-λ 1 (-if (-x 0) (-x 0) b)) (list a) _)
       (match* ((go ctx a) (go (append (vars-not-in 1 ctx) ctx) b))
         [(`(or ,l ...) `(or ,r ...)) `(or ,@(cast l Sexps) ,@(cast r Sexps))]
         [(`(or ,l ...) r) `(or ,@(cast l Sexps) ,r)]
         [(l `(or ,r ...)) `(or ,l ,@(cast r Sexps))]
         [(l r) `(or ,l ,r)])]
      [(-@ (-st-mk (-id (and n (or 'and/c 'or/c 'not/c)) 'Λ) _) c* _) `(,n ,@(map (curry go ctx) c*))]
      #| TODO obsolete? 
      [(-if (and e (-•ₗ α)) e₁ e₂)
       (match (σ@ σ α)
         [(-b #f) (go ctx e₂)]
         [(not '•) (go ctx e₁)]
         [_ `(if ,(go ctx e) ,(go ctx e₁) ,(go ctx e₂))])]
      |#
      [(-if a b (-b #f))
       (match* ((go ctx a) (go ctx b))
         [(`(and ,l ...) `(and ,r ...)) `(and ,@(cast l Sexps) ,@(cast r Sexps))]
         [(`(and ,l ...) r) `(and ,@(cast l Sexps) ,r)]
         [(l `(and ,r ...)) `(and ,l ,@(cast r Sexps))]
         [(l r) `(and ,l ,r)])]
      [(-if a b (-b #t)) `(implies ,(go ctx a) ,(go ctx b))]

      [(-λ (? integer? n) e)
       (define x* (vars-not-in n ctx))
       `(λ ,(reverse x*) ,(go (append x* ctx) e))]
      [(-λ (cons n _) e)
       (match-define (and x* (cons x₁ xs)) (vars-not-in (+ 1 n) ctx))
       `(λ (,(reverse xs) . ,x₁) ,(go (append x* ctx) e))]
      [(-•ₗ n) `(• ,n)]
      [(-b b) (show-b b)]
      [(-st-mk t _) (-id-name t)]
      [(-st-ac (-id 'cons 'Λ) _ 0) 'car]
      [(-st-ac (-id 'cons 'Λ) _ 1) 'cdr]
      [(-st-ac t _ i) (string->symbol (format "~a@~a" (-id-name t) i))]
      [(-st-p t _) (string->symbol (format "~a?" (-id-name t)))]
      [(? -o? o) (name o)]
      [(-x i) (ctx-ref ctx i)]
      [(-ref x _) (-id-name x)]
      [(-let-values _ _ _) '(let-values …) #|TODO|#]
      [(-@ f xs _) `(,(go ctx f) ,@(map (curry go ctx) xs))]
      [(-@-havoc x) `(apply ,(go ctx x) •)]
      [(-begin es) `(begin ,@(map (curry show-e σ) es))]
      [(-begin0 e es) `(begin ,(show-e σ e) ,@(map (curry show-e σ) es))]
      #;[(-apply f xs _) `(@ ,(go ctx f) ,(go ctx xs))]
      [(-if i t e) `(if ,(go ctx i) ,(go ctx t) ,(go ctx e))]
      [(-amb e*) `(amb ,@(for/list : (Listof Sexp) ([e e*]) (go ctx e)))]
      [(-μ/c x c) `(μ/c (,x) ,(go ctx c))]
      [(-->i c d v?) `(,@(map (curry go ctx) c) ,(if v? '↦* '↦) ,(go ctx d))]
      [(-x/c x) x]
      [(-struct/c t cs) `(,(string->symbol (format "~a/c" (-id-name t))) ,@(map (curry go ctx) cs))])))

(define (inlinable? [e : -expr]) : Boolean
  (or (-x? e) (-ref? e) (-prim? e)))

(: show-b : (U Number String Boolean Symbol Keyword) → Sexp)
(define (show-b x)
  (cond
   [(string? x) (format "\"~a\"" x)]
   [(or (symbol? x) (keyword? x)) `(quote ,x)]
   [(and (real? x) (inexact? x))
    (define s (number->string x))
    (substring s 0 (min (string-length s) 5))]
   [else x]))

(: show-σ : -σ → (Listof Sexp))
(define (show-σ σ)
  (for/list ([(α Vs) (in-hash σ)])
    `(,(show-α σ α) ↦ ,@(show-Vs σ Vs))))

(: ctx-ref : (Listof Symbol) Integer → Symbol)
;; Returns the `i`th symbol in the list if it is in there, or "…ₖ" for a `k` index out of range
(define (ctx-ref xs i)
  (let go ([xs xs] [i i])
    (match* (xs i)
      [('() _) (string->symbol (format "…~a" (n-sub i)))]
      [((cons x _) 0) x]
      [((cons _ xr) i) (go xr (- i 1))])))
