#lang typed/racket/base
(require racket/match racket/list racket/set racket/function
         "utils.rkt" "lang.rkt" "runtime.rkt")

(provide (all-defined-out))

(define-type Sexps (Listof Sexp))

(: show-Ans : -σ -Ans → Sexp)
(define (show-Ans σ Ans)
  (cond
    [(-W? Ans) (show-A σ (-W-x Ans))]
    [else (for/list : (Listof Sexp) ([W Ans])
            (show-V σ (-W-x W)))]))

(: show-A : -σ -A → Sexp)
(define (show-A σ A)
  (match A
    [(-blm l+ lo V C) `(blame ,l+ ,lo ,(show-V σ V) ,(show-Vs σ C))]
    [(? list? Vs) (show-Vs σ Vs)]))

(: show-Vs : -σ (Sequenceof -V) → (Listof Sexp))
(define (show-Vs σ Vs)
  (for/list : (Listof Sexp) ([V Vs]) (show-V σ V)))

(: show-V : -σ -V → Sexp)
(define (show-V σ V)
  (match V
    ['undefined 'undefined]
    [(-b b) (show-b b)]
    ['• '●]
    [(? -o? o) (show-o o)]
    [(-Clo xs e _ _) (show-e σ (-λ xs e))]
    [(-Ar γ α _) `(,(show-α σ γ) ◃ ,(show-α σ α))]
    #| TODO obsolete?
    [(-st (-id 'not/c 'Λ) (list (.// (-λ↓ (-λ 1 (-@ '= (list (-x 0) e) _)) _) _))) `(≠/c ,(show-e σ e))]
    [(-st (-id t 'Λ) (list)) t]
    [(-st (-id (and n (or 'and/c 'or/c)) 'Λ) V*) `(,n ,@(show-Vs σ V*))]
    [(-st (-id 'not/c 'Λ) V*) `(not/c ,@(show-Vs σ V*))]
    |#
    [(-St t αs) `(,(-id-name t) ,@(show-αs σ αs))]
    [(-=> γs α) `(,@(show-αs σ γs) ↦ ,(show-α σ α))]
    [(-=>i doms e ρ Γ) `(,@(for/list : (Listof Sexp) ([dom doms])
                              (match-define (cons x γ) dom)
                              `(,x : ,(show-α σ γ)))
                          ↦ ,(show-e σ e))]
    [(-St/C t αs) `(,(string->symbol (format "~a/c" (-id-name t))) ,@(show-αs σ αs))]
    [(-μ/C x α) `(μ/C (,x) ,(show-α σ α))]
    [(-X/C α) `(X: ,(show-α σ α))]))

(: show-αs : -σ (Listof -α) → (Listof Sexp))
(define (show-αs σ αs) (map (curry show-α σ) αs))

(: show-α : -σ -α → Sexp)
(define (show-α σ α)
  (match α
    [(-α.top id) (-id-name id)]
    [(-α.bnd ctx ctn) `(α ,(show-e σ ctx) ,@(map (curry show-ctn σ) ctn))]))

(: show-ctn : -σ -ctn → Sexp)
(define (show-ctn σ ctn)
  (cond
    [(-e? ctn) (show-e σ ctn)]
    [(-π? ctn) (show-π ctn)]
    [(set? ctn) (show-Γ ctn)]
    [else ctn]))

(: show-π : -π* → Sexp)
(define (show-π π)
  (cond
    [(-π@? π)
     `(@ ,(show-π (-π@-f π))
         ,@(for/list : (Listof Sexp) ([x (-π@-xs π)]) (show-π x)))]
    [(-id? π) (-id-name π)]
    [π (show-e -σ∅ π)]
    [else '⊘]))

(: show-Γ : -Γ → (Listof Sexp))
(define (show-Γ Γ)
  (for/list : (Listof Sexp) ([π Γ]) (show-π π)))

(: show-ρ : -σ -ρ → (Listof Sexp))
(define (show-ρ σ ρ)
  (for/list ([(x α) (in-hash ρ)])
    `(,x ↦ ,(show-α σ α))))

(: show-E : -σ -E → Sexp)
(define (show-E σ E)
  (match E
    [(? -A? A) (show-A σ A)]
    [(-↓ e _) (show-e σ e)]))

(: show-e : -σ -e → Sexp)
(define (show-e σ e)
  (let go ([e e])
    (match e
      ; syntactic sugar
      [(-λ (list x) (-@ '= (list (-x x) e*) _)) `(=/c ,(go e*))]
      [(-λ (list x) (-@ 'equal? (list (-x x) e*) _)) `(≡/c ,(go e*))]
      [(-λ (list x) (-@ '> (list (-x x) e*) _)) `(>/c ,(go e*))]
      [(-λ (list x) (-@ '< (list (-x x) e*) _)) `(</c ,(go e*))]
      [(-λ (list x) (-@ '>= (list (-x x) e*) _)) `(≥/c ,(go e*))]
      [(-λ (list x) (-@ '<= (list (-x x) e*) _)) `(≤/c ,(go e*))]
      [(-λ (list x) (-@ (? closed? f) (list (-x x)) _)) (go f)]
      [(-λ (list x) (-@ 'arity-includes? (list (-x x) (-b 0)) _)) `(arity-includes/c ,x)]
      [(-λ (list x) (-@ 'arity=? (list (-x x) (-b 0)) _)) `(arity=/c ,x)]
      [(-λ (list x) (-@ 'arity>=? (list (-x x) (-b 0)) _)) `(arity≥/c ,x)]
      #;[(-@ (-st-mk 'or/c _) (list (-@ (-st-mk 'not/c _) (list c) _) d) _)
       `(⇒/c ,(go ctx c) ,(go ctx d))]
      [(-λ (list _) (-b (not #f))) 'any/c]
      [(-λ (list _) (-b #f)) 'none/c]
      [(-@ (-st-mk (-id 'null 'Λ) 0) (list) _) 'null]
      [(-@ (-λ (list x) (-x x)) (list e) _) (go e)]
      [(-@ (-λ (list x) (-if (-x x) (-x x) b)) (list a) _)
       (match* ((go a) (go b))
         [(`(or ,l ...) `(or ,r ...)) `(or ,@(cast l Sexps) ,@(cast r Sexps))]
         [(`(or ,l ...) r) `(or ,@(cast l Sexps) ,r)]
         [(l `(or ,r ...)) `(or ,l ,@(cast r Sexps))]
         [(l r) `(or ,l ,r)])]
      [(-@ (-st-mk (-id (and n (or 'and/c 'or/c 'not/c)) 'Λ) _) c* _) `(,n ,@(map go c*))]
      #| TODO obsolete? 
      [(-if (and e (-•ₗ α)) e₁ e₂)
       (match (σ@ σ α)
         [(-b #f) (go ctx e₂)]
         [(not '•) (go ctx e₁)]
         [_ `(if ,(go ctx e) ,(go ctx e₁) ,(go ctx e₂))])]
      |#
      [(-if a b (-b #f))
       (match* ((go a) (go b))
         [(`(and ,l ...) `(and ,r ...)) `(and ,@(cast l Sexps) ,@(cast r Sexps))]
         [(`(and ,l ...) r) `(and ,@(cast l Sexps) ,r)]
         [(l `(and ,r ...)) `(and ,l ,@(cast r Sexps))]
         [(l r) `(and ,l ,r)])]
      [(-if a b (-b #t)) `(implies ,(go a) ,(go b))]

      [(-λ (list xs ...) e) `(λ ,xs ,(go e))]
      [(-λ (-varargs xs rest) e) `(λ ,(cons xs rest) ,(go e))]
      [(-•ₗ n) `(• ,n)]
      [(-b b) (show-b b)]
      [(-st-mk t _) (-id-name t)]
      [(-st-ac (-id 'cons 'Λ) _ 0) 'car]
      [(-st-ac (-id 'cons 'Λ) _ 1) 'cdr]
      [(-st-ac t _ i) (string->symbol (format "~a@~a" (-id-name t) i))]
      [(-st-p t _) (string->symbol (format "~a?" (-id-name t)))]
      [(? -o? o) (show-o o)]
      [(-x x) x]
      [(-ref x _) (-id-name x)]
      [(-let-values _ _ _) '(let-values …) #|TODO|#]
      [(-@ f xs _) `(,(go f) ,@(map go xs))]
      [(-@-havoc x) `(apply ,(go x) •)]
      [(-begin es) `(begin ,@(map (curry show-e σ) es))]
      [(-begin0 e es) `(begin ,(show-e σ e) ,@(map (curry show-e σ) es))]
      #;[(-apply f xs _) `(@ ,(go ctx f) ,(go ctx xs))]
      [(-if i t e) `(if ,(go i) ,(go t) ,(go e))]
      [(-amb e*) `(amb ,@(for/list : (Listof Sexp) ([e e*]) (go e)))]
      [(-μ/c x c) `(μ/c (,x) ,(go c))]
      [(-->  doms rng) `(,@(map go doms) ↦ ,(go rng))]
      [(-->i doms rng) `(,@(for/list : (Listof Sexp) ([dom doms])
                             (match-define (cons x c) dom)
                             `(,x : ,(go c)))
                         ↦ ,(go rng))]
      [(-x/c x) x]
      [(-struct/c t cs) `(,(string->symbol (format "~a/c" (-id-name t))) ,@(map go cs))])))

(: show-o : -o → Symbol)
;; Return operator's simple show-o for pretty-printing
(define show-o
  (match-lambda
   [(? symbol? s) s]
   [(-st-mk (-id t _) _) t]
   [(-st-ac (-id 'cons 'Λ) 2 0) 'car]
   [(-st-ac (-id 'cons 'Λ) 2 1) 'cdr]
   [(-st-ac (-id 'box 'Λ) 1 0) 'unbox]
   [(-st-ac (-id t _) _ i) (string->symbol (format "~a@~a" t i))]
   [(-st-p (-id t _) _) (string->symbol (format "~a?" t))]))

(define (inlinable? [e : -e]) : Boolean
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
