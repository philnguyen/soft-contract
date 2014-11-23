#lang typed/racket/base
(provide parse)
(require racket/match racket/set racket/list "utils.rkt" "lang.rkt")

;; Informal syntax description:
; p ::= (m ... mₙ)
; m ::= (module name L (provide (contract-out prov ...)) (require req ...) def-struct ... def ...)
; L ::= racket/base
; prov ::= (x c) | (struct x ([x c] ...))
; req  ::= (only-in module-name name ...) | module-name
; def-struct ::= (struct x (x ...))
; def  ::= (define x e) | (define (f x) e) | (define x •)
; e ::= v | x | xˡ | (e e ...)ˡ | (if e e e) | (let ([x e] ...) e) | (let* ([x e] ...) e)
;     | (and/c e e) | (or/c e e) | (struct/c x (e ...)) | (not/c e)
;     | (one-of/c e ...) | (->i ([x c] ...) (y (x ...) c))
;     | (box/c e)
;     | (recursive-contract e)

(define-type Ex-Def (Map L (Pairof (Setof Symbol) (Setof Symbol))))
(define-type Im (Map L (Map Symbol L)))
(define-type Ctx (Setof Symbol))
(define ctx∅ : Ctx ∅)

(: parse : Any → -p)
;; Convert S-exp to internal AST representation
(define (parse s)
  (let* ([ex/def (pass₁ s)]
         [im (pass₂ s ex/def)])
    (pass₃ s ex/def im)))

(: pass₁ : Any → Ex-Def)
;; First pass computes each module's provide/define set
(define (pass₁ s)
  
  (: pass₁/prov : Any → (Setof Symbol))
  (define (pass₁/prov s)
    (match s
      [`(struct ,(? symbol? t) ([,(? symbol? fs) ,_] ...))
       (struct-names t (cast fs (Listof Symbol)))]
      [`(,(? symbol? x) ,_) {set x}]
      [_ (error "Invalid provide clause:" s)]))
  
  (: pass₁/m : (Listof Any) → (Values (Setof L) (Setof L)))
  (define (pass₁/m m-clauses)
    (for/fold ([provs : (Setof Symbol) ∅] [defs : (Setof Symbol) ∅]) ([c m-clauses])
      (match c
        [`(provide (contract-out ,prov-clauses ...))
         (values (for/fold ([provs provs]) ([c prov-clauses])
                   (set-union provs (pass₁/prov c)))
                 defs)]
        [`(struct ,(? symbol? t) (,f ...))
         (values provs (set-union defs (struct-names t (cast f (Listof Symbol)))))]
        [`(define ,(? symbol? x) ,_) (values provs (set-add defs x))]
        [`(define (,(? symbol? f) ,_ ...) ,_) (values provs (set-add defs f))]
        [_ (values provs defs)])))
  
  (match s
    [(list m ...) (for/fold ([ex/def : Ex-Def (hash)]) ([mᵢ m])
                    (match-let ([`(module ,(? symbol? l) racket/base ,m-clauses ...) mᵢ])
                      (define-values (provs defs) (pass₁/m m-clauses))
                      (hash-set-new ex/def l (cons provs defs)
                                    (λ (_) (format "Module ~a is defined twice" l)))))]
    [_ (error "Invalid program syntax:" s)]))

(: pass₂ : Any Ex-Def → Im)
;; Second pass resolves imported identifiers
(define (pass₂ s ex/def)
  
  (: pass₂/m : Any (Map Symbol L) L → (Map Symbol L))
  (define (pass₂/m s im l)
    (define my-defs (cdr (hash-ref ex/def l)))
    
    (: pass₂/req : Any (Map Symbol L) → (Map Symbol L))
    (define (pass₂/req s im)
      (match s
        [`(only-in ,(? symbol? m) ,(? symbol? x) ...)
         (match (hash-ref ex/def m #f)
           [#f (errorf "Module `~a` requires undefine module `~a`" l m)]
           [(cons provs _)
            (for/fold ([im im]) ([xᵢ x])
              (cond
               [(not (symbol? xᵢ))
                (errorf "Module `~a`'s require clause: Expect identifier, given `~a`" l xᵢ)]
               [(set-member? my-defs xᵢ)
                (errorf "Module `~a` defines `~a` and still imports it from module `~a`" l xᵢ m)]
               [(set-member? provs xᵢ)
                (hash-set-new
                 im xᵢ m
                 (λ ([m₀ : Symbol])
                   (format "Module `~a` requires `~a` from both `~a` and `~a`" l xᵢ m₀ m)))]
               [else (errorf "Module `~a` requires non-existent identifer `~a` from `~a`" l xᵢ m)]))])]
        [(? symbol? m)
         (match (hash-ref ex/def m #f)
           [#f (errorf "Module `~a` requires undefined module `~a`" l m)]
           [(cons provs _) (pass₂/req `(only-in ,m ,@(set->list provs)) im)])]
        [_ (error "Invalid require clause:" s)]))
    
    (match s
      [`(require ,req-clauses ...) (for/fold ([im im]) ([c req-clauses])
                                     (pass₂/req c im))]
      [_ im]))
  
  (match s
    [(list m ...)
     (for/fold ([im : Im (hash)]) ([mᵢ m])
       (match-let ([`(module ,(? symbol? l) racket/base ,m-clauses ...) mᵢ])
         (hash-set im l (for/fold ([m : (Map Symbol L) (hash)]) ([c m-clauses])
                          (pass₂/m c m l)))))]
    [_ (error "Invalid program syntax:" s)]))

(: pass₃ : Any Ex-Def Im → -p)
;; Third pass parses expressions
(define (pass₃ s ex/def im)
  
  (: pass₃/m : Any → -m)
  (define (pass₃/m s)
    (match s
      [`(module ,(? symbol? l) racket/base ,m-clauses ...)
       (define-values (provs defs)
         (for/fold ([provs : (Listof (Pairof Symbol -e)) '()]
                    [defs : (Listof (Pairof Symbol -e))'()])
                   ([c m-clauses])
           (match c
             [`(provide (contract-out ,prov-clauses ...))
              (values (for/fold ([provs provs]) ([c prov-clauses])
                        (pass₃/prov provs c l))
                      defs)]
             [`(provide ,_ ...)
              (errorf "In module `~a`: (provide (contract-out _ ...)) is the only provide form supported for now" l)]
             [`(require ,_ ...) (values provs defs)]
             [`(struct ,(? symbol? t) (,(? symbol? f) ...))
              (values provs
                      (let ([n (length f)])
                        (append (list* (cons t (-struct/cons t n))
                                       (cons (struct-pred-name t) (-struct/pred t n))
                                       (struct-accs t (cast f (Listof Symbol))))
                                defs)))]
             [`(define ,(? symbol? x) ,(or '● '• 'opq))
              (values provs (cons (cons x '●) defs))]
             [`(define (,(? symbol? f) ,(? symbol? x) ...) ,e)
              (values provs
                      (cons (cons f (pass₃/e `(λ ,x ,e) l ctx∅)) defs))]
             [`(define ,(? symbol? x) ,e)
              (values provs
                      (cons (cons x (pass₃/e e l ctx∅)) defs))]
             [s (error "Invalid module clause:" s)])))
       (-m l
           (reverse provs)
           (hash->list (hash-invert (hash-ref im l)))
           (let ([defs (reverse defs)])
             (cond [(empty? defs)
                    (errorf "Module `~a` must at least define or provide one name" l)]
                   [else defs])))]))
  
  (: pass₃/prov : (Listof (Pairof Symbol -e)) Any L → (Listof (Pairof Symbol -e)))
  (define (pass₃/prov provs c l)
    (match c
      [`(struct ,(? symbol? t) ([,(? symbol? x) ,c] ...))
       (define cs (for/list : (Listof -e) ([cᵢ c]) (pass₃/e cᵢ l ctx∅)))
       (define d (-struct/c t cs))
       (append (list* (cons t (-λ/c (for/list ([xᵢ x] [cᵢ cs]) (cons (cast xᵢ Symbol) cᵢ)) d))
                      (cons (struct-pred-name t) -pred/c)
                      (for/list : (Listof (Pairof Symbol -e))
                                ([acc (struct-accs t (cast x (Listof Symbol)))] [cᵢ cs])
                        (cons (car acc) (-λ/c (list (cons '•₀ d)) cᵢ))))
               provs)]
      [`(,(? symbol? x) ,c) (cons (cons x (pass₃/e c l ctx∅)) provs)]
      [_ (error "Invalid provide clause:" c)]))
  
  (: pass₃/e : Any L Ctx → -e)
  (define (pass₃/e s l ρ)
    (match s
      ;; Synactic sugar
      [`(and) -tt]
      [`(and ,s) (pass₃/e s l ρ)]
      [`(and ,s ,sᵣ ...) (-if (pass₃/e s l ρ) (pass₃/e `(and ,@sᵣ) l ρ) -ff)]
      [`(or) -ff]
      [`(or ,s) (pass₃/e s l ρ)]
      [`(or ,s ,sᵣ ...) (-let (list (cons (genₓ 0) (pass₃/e s l ρ)))
                              (-if (+x 0) (+x 0) (pass₃/e `(or ,@sᵣ) l ρ)))]
      [`(let* () ,s) (pass₃/e s l ρ)]
      [`(let* ((,(? symbol? x) ,sₓ) ,b ...) ,s)
       (-let (list (cons x (pass₃/e sₓ l ρ)))
             (pass₃/e `(let ,b ,s) l (set-add ρ x)))]
      [`(begin ,s ... ,s′) (-let (for/list ([i (in-naturals)] [sᵢ s])
                                   (cons (genₓ (cast i ℕ)) (pass₃/e sᵢ l ρ)))
                                 (pass₃/e s′ l ρ))]
      [`(list ,s* ...)
       (foldr (λ ([sᵢ : Any] [e : -e])
                (-@ l -cons (list (pass₃/e sᵢ l ρ) e)))
              -empty
              s*)]
      ;; Normal ones
      [(or) (error "for some reason this useless line speeds up compile time...")]
      [`(,(or 'λ 'lambda) (,(? symbol? x) ...) ,e)
       (-λ (cast x (Listof Symbol))
           (pass₃/e e l (set-add/l ρ (cast x (Listof Symbol)))))]
      [`(if ,e ,e₁ ,e₂) (-if (pass₃/e e l ρ) (pass₃/e e₁ l ρ) (pass₃/e e₂ l ρ))]
      [`(let ,(list `[,(? symbol? x) ,eₓ] ...) ,e)
       (-let (for/list ([xᵢ x] [eᵢ eₓ])
               (cons (cast xᵢ Symbol) (pass₃/e eᵢ l ρ)))
             (pass₃/e e l (set-add/l ρ (cast x (Listof Symbol)))))]
      [`(recursive-contract ,c) (-rec/c (pass₃/e c l ρ))]
      [`(-> ,c ... ,d)
       (-λ/c (for/list ([i #|TODO why can't ann ℕ|# (in-naturals)] [cᵢ c])
               (cons (string->symbol (format "•~a" (subscript (cast i ℕ))))
                     (pass₃/e cᵢ l ρ)))
             (pass₃/e d l ρ))]
      [`(->i ([,(? symbol? x) ,c] ...) (,(? symbol? y) ,_ ,d))
       (-λ/c (for/list ([xᵢ x] [cᵢ c])
               (cons (cast xᵢ Symbol) (pass₃/e cᵢ l ρ)))
             (pass₃/e d l (set-add/l ρ (cast x (Listof Symbol)))))]
      [`(struct/c ,(? symbol? t) (,c ...))
       (-struct/c t (for/list ([cᵢ c]) (pass₃/e cᵢ l ρ)))]
      [`(and/c ,c ...) (-and/c l (for/list ([cᵢ c]) (pass₃/e cᵢ l ρ)))]
      [`(or/c ,c ...) (-or/c l (for/list ([cᵢ c]) (pass₃/e cᵢ l ρ)))]
      [`(not/c ,c) (-not/c l (pass₃/e c l ρ))]
      [`(box ,s) (-box (pass₃/e s l ρ))]
      [`(unbox ,s) (-unbox l (pass₃/e s l ρ))]
      [`(set-box! ,s ,t) (-set-box! l (pass₃/e s l ρ) (pass₃/e t l ρ))]
      [`(vector ,s ...) (-vector (for/list ([sᵢ s]) (pass₃/e sᵢ l ρ)))]
      [`(vector-ref ,s ,i) (-vector-ref l (pass₃/e s l ρ) (pass₃/e i l ρ))]
      [`(vector-set! ,s ,i ,t)
       (-vector-set! l (pass₃/e s l ρ) (pass₃/e i l ρ) (pass₃/e t l ρ))]
      [(list f xs ...) (-@ l (pass₃/e f l ρ) (for/list ([x xs]) (pass₃/e x l ρ)))]
      [#f -ff]
      [#t -tt]
      [(? ℂ? x) (+b x)]
      [(? string? x) (+b x)]
      [(? symbol? x)
       (cond
        [(set-member? ρ x) (+x x)]
        [(set-member? (cdr (hash-ref ex/def l)) x) (-ref l x l)]
        [else (match (hash-ref (hash-ref im l) x #f)
                [#f (or (+prim x)
                        (errorf "Module `~a` has free variable `~a`" l x))]
                [(? symbol? h) (-ref l x h)])])]))

  (match s
    [(list m₁ m ...) (cons (pass₃/m m₁) (map pass₃/m m))]
    [_ (error "Program must be non-empty sequence of modules")]))

(: struct-names : Symbol (Listof Symbol) → (Setof Symbol))
(define (struct-names t fs)
  (for/fold ([s : (Setof Symbol) {set t (struct-pred-name t)}]) ([f fs])
    (set-add s (string->symbol (format "~a-~a" t f)))))

(define (struct-pred-name t)
  (string->symbol (format "~a?" t)))

;; Generate list of accessor name and accessors
(: struct-accs : Symbol (Listof Symbol) → (Listof (Pairof Symbol -struct/acc)))
(define (struct-accs t fs)
  (define n (length fs))
  (for/list ([fᵢ fs] [i n])
    (cons (string->symbol (format "~a-~a" t fᵢ)) (-struct/acc t n i))))

;; Return common (syntactic) values from their names
(define/memoeq (+prim [name : Symbol]) : (Option -e)
  (match name
    [(? -o? o) o]
    ['cons? -cons?]
    ['empty? -empty/c]
    ['car -car]
    ['cdr -cdr]
    ['cons -cons]
    ['empty -empty]
    ['void (-struct/cons 'void 0)]
    ['void? (-struct/pred 'void 0)]
    ['>= '≥]
    ['<= '≤]
    ['any -any/c]
    ['any/c -any/c]
    ['none/c -none/c]
    [_ #f]))
