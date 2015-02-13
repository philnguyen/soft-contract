#lang racket/base
(require racket/match racket/list racket/set racket/contract
         "utils.rkt" "lang.rkt" (only-in redex/reduction-semantics variable-not-in))
(provide read-p on-•! -begin)

(define on-•! (make-parameter (λ () '•)))

;; figure out define/provide/require for each module
(define (pass-1 p)

  ;; module-clause -> (Values Symbol-Set Symbol-Set Symbol-Set)
  (define (pass-1/m-clause m-clause)
    (match m-clause
      [`(require (submod ".." ,x*) ...)
       (values ∅ ∅ (list->set x*))]
      [`(provide/contract ,p/c-items ...)
       (pass-1/m-clause `(provide (contract-out ,@p/c-items)))]
      [`(provide ,provide-specs ...)
       (values
        ∅
        (for/fold ([decs ∅]) ([provide-spec (in-list provide-specs)])
          (match provide-spec
            [(? symbol? s) (set-add decs s)]
            [`(contract-out ,p/c-items ...)
             (for/fold ([decs ∅]) ([p/c-item (in-list p/c-items)])
               (match p/c-item
                 [`(struct ,t ([,field* ,_] ...)) (set-union decs (gen-names t field*))]
                 [`(,(? symbol? x) ,_) (set-add decs x)]
                 [_
                  (error
                   'Parser
                   "expect contracted clause as one of:~n (id contract)~n (struct id ([id contract] …))~ngiven:~n~a"
                   (pretty p/c-item))]))]
            [_
             (error
              'Parser
              "expect provide spec as one of:~n id~n (contract-out p/c-item …)~ngiven:~a"
              (pretty provide-spec))]))
        ∅)]
      [(or `(define (,f ,_ ...) ,_) `(define ,f ,_))
       (values {set f} ∅ ∅)]
      [`(struct ,t (,field* ...))
       (values (gen-names t field*) ∅ ∅)]
      [_ (error
          'Parser
          "expect one of:~n (require (submod \"..\" module-name) …)~n (provide provide-spec …)~n (define x v)~n (struct id (id …))~ngiven:~n~a"
          (pretty m-clause))]))

  (match p
    [`(,m* ... (require (quote ,main-reqs) ...) ,_ ...)
     (for/fold ([M (hash '† (list ∅ ∅ (list->set main-reqs)))]) ([m m*])
       (match m
         [`(module ,name racket ,d* ...)
          (hash-set
           M
           name
           (let ()
             (define-values (defs decs reqs)
               (for/fold ([defs ∅] [decs ∅] [reqs ∅]) ([d d*])
                 (define-values (defs′ decs′ reqs′) (pass-1/m-clause d))
                 (values (set-union defs defs′)
                         (set-union decs decs′)
                         (set-union reqs reqs′))))
             (list defs decs reqs)))]
         [_ (error 'Parser "expect module definition of the form~n (module module-name racket _ …)~ngiven:~n~a" (pretty m))]))]
    [`(,_ ... ,(and req `(require ,_ ...)) ,_ ...)
     (error 'Parser "expect require clause of form (require 'name …)~ngiven:~n ~a" req)]
    [`(,(and modl `(module ,_ racket ,_ ...)) ... ,e ...)
     (pass-1 `(,@modl (require) ,@e))]))

;; read and return program's ast
(define (read-p p)
  #;(log-debug "~a~n~n" p)
  (match p
    [`((module ,l* racket ,d** ...) ... (require ,_ ...) ,e ...)
     (define syms (pass-1 p))
     (define ms (for/hash ([l l*] [d* d**]) (values l (read-m syms l d*))))
     (define accs (gen-accs (hash-values ms)))
     (.p (.m* l* ms) accs (read-e syms '† '() (-begin e)))]
    [`(,(and m `(module ,_ racket ,_ ...)) ... ,e ...) (read-p `(,@m (require) ,@e))]
    [_ (error 'Parser "invalid program form. Expect~n((module module-name racket~n (provide (contract-out (x c) …))~n (require (submod \"..\" module-name) …)~n (define x v) …) …).~ngiven:~n~a"
              (pretty p))]))

(define -begin
  (match-lambda
   [(list) '(void)]
   [(list e) e]
   [(list e ...) (cons 'begin e)]))

(define h∅ (hash))

;; read and return module's ast
(define (read-m syms l ds)

  (define (read-m-clause decs defs order m-clause)
    (match m-clause
      [`(provide/contract ,p/c-items ...)
       (read-m-clause decs defs order `(provide (contract-out ,@p/c-items)))]
      [`(provide ,provide-specs ...)

       (define (read-provide-spec decs spec)
         (match spec
           [(? symbol? s) (read-provide-spec decs `(contract-out (,s any/c)))]
           [`(contract-out ,p/c-items ...)
            (for/fold ([decs decs]) ([p/c-item (in-list p/c-items)])
              (match p/c-item
                [`(struct ,t ([,field* ,c*] ...))
                 (define field-cs (for/list ([c c*]) (read-e syms l '() c)))
                 (define strct-c (.struct/c t field-cs))
                 (for/fold ([decs (hash-set*
                                   decs
                                   t (.λ/c field-cs strct-c #f)
                                   (gen-p t) .any/c #;.pred/c)])
                           ([field field*] [field-c field-cs])
                   (hash-set decs (gen-ac t field) (.λ/c (list strct-c) field-c #f)))]
                [`(,x ,c) (hash-set decs x (read-e syms l '() c))]))]))

       (values
        (for/fold ([decs decs]) ([spec (in-list provide-specs)])
          (read-provide-spec decs spec))
        defs
        order)]
      [`(define* (,f ,x ... ,z) ,e)
       (values decs (hash-set defs f (read-e syms l '() `(λ* (,@x ,z) ,e))) (cons f order))]
      [`(define (,f ,x ...) ,e)
       (values decs (hash-set defs f (read-e syms l '() `(λ ,x ,e))) (cons f order))]
      [`(define ,x ,v)
       (values decs (hash-set defs x (read-e syms l '() v)) (cons x order))]
      [`(struct ,t (,field* ...))
       (define n (length field*))
       (values decs
               (for/fold ([defs (hash-set*
                                 defs
                                 t (.st-mk t n)
                                 (gen-p t) (.st-p t n))])
                         ([field field*] [i (in-naturals)])
                 (hash-set defs (gen-ac t field) (.st-ac t n i)))
               (append (for/list ([f field*]) (gen-ac t f))
                       (list* (gen-p t) t order)))]
      [_ (values decs defs order)]))

  ;; read each provide/define clause
  (define-values (decs defs rev-order)
    (for/fold ([decs h∅] [defs h∅] [order empty]) ([d ds])
      (read-m-clause decs defs order d)))

  ;; rebuild table from definitions
  (define m1
    (for/hash ([(l e) (in-hash defs)])
      (values l (cons e (hash-ref decs l #f)))))

  ;; undefined but declared values are •
  (define-values (m2 ro)
    (for/fold ([m m1] [ro rev-order])
              ([(l c) (in-hash decs)] #:unless (hash-has-key? m1 l))
      (values (hash-set m l (cons ((on-•!)) c)) (cons l ro))))

  (.m (reverse ro) m2))

(define (read-e syms l xs e)
  (define (go ei) (read-e syms l xs ei))

  ;; FIXME temporary hack to allow shadowing
  (define hack? (or/c '>=/c '>/c '<=/c '</c '=/c))

  (define/contract (resolve-symbol s)
    (symbol? . -> . (or/c #f .e?))
    (or (var xs s)
        (match-let ([(list my-defs my-decs my-reqs) (hash-ref syms l)])
          (or (for*/first ([name my-defs] #:when (eq? name s)) (.ref s l l))
              (for*/first ([name my-decs] #:when (eq? name s)) (.ref s l l))
              (for*/first ([l-req my-reqs]
                           [their-provides (in-value (second (hash-ref syms l-req)))]
                           #:when (set-member? their-provides s))
                (.ref s l-req l))
              (prim s)
              (match s ; desugar these for more uniform treatment of arithmetics
                ['zero? (.λ 1 (.@ '= (list (.x 0) .zero) l) #f)]
                ['positive? (.λ 1 (.@ '> (list (.x 0) .zero) l) #f)]
                ['negative? (.λ 1 (.@ '< (list (.x 0) .zero) l) #f)]
                [_ #f])))))

  (match e ; assume `♣` never appears in source code
    [`(,(? hack? c) ,e)
     (match (resolve-symbol c)
       [(? .e? f) (.@ f (list (go e)) l)]
       [_
        (match `(,c ,e)
          [`(>=/c ,e) (go `(λ (♣) (and (real? ♣) (>= ♣ ,e))))]
          [`(>/c ,e) (go `(λ (♣) (and (real? ♣) (> ♣ ,e))))]
          [`(<=/c ,e) (go `(λ (♣) (and (real? ♣) (<= ♣ ,e))))]
          [`(</c ,e) (go `(λ (♣) (and (real? ♣) (< ♣ ,e))))]
          [`(=/c ,e) (go `(λ (♣) (and (real? ♣) (= ♣ ,e))))])])]
    ;; syntactic sugar
    [`(and) .tt]
    [`(and ,e) (go e)]
    [`(and ,e1 ,er ...) (.if (go e1) (go `(and ,@er)) .ff)]
    [`(or) .ff]
    [`(or ,e) (go e)]
    [`(or ,e1 ,er ...) (go `(let ([♣ ,e1]) (if ♣ ♣ (or ,@er))))]
    [`(implies ,e1 ,e2) (.if (go e1) (go e2) .tt)]
    [`(begin) (.b #f)] ; dummy
    [`(begin ,e) (go e)]
    [`(begin ,e* ...) (.@ (.λ (length e*) (.x 0) #f) (map go e*) l)]
    [`(cond [else ,e]) (go e)]
    [`(cond [,e1 ,e2] ,p ...) (.if (go e1) (go e2) (go `(cond ,@p)))]
    [`(let ([,x ,ex] ...) ,e) (go `((λ ,x ,e) ,@ex))]
    [`(let* () ,e) (go e)]
    [`(let* ([,x ,ex] ,p ...) ,e) (go `(let ([,x ,ex]) (let* ,p ,e)))]
    [`(list ,e* ...)
     (foldr (λ (ei acc) (.@ (prim 'cons) (list (go ei) acc) l)) (prim 'empty) e*)]
    [`(and/c ,e* ...) (.and/c l (map go e*))]
    [`(or/c ,e* ...) (.or/c l (map go e*))]
    [`(not/c ,c) (.not/c l (go c))]
    [`(=>/c ,c ,d) (.or/c l (list (.not/c l (go c)) (go d)))]
    [`(cons/c ,c ,d) (.struct/c 'cons (list (go c) (go d)))]
    [`(listof ,c)
     (let ([x (variable-not-in c 'X)])
       (.μ/c x (.or/c l (list .empty/c (.cons/c (go c) (.x/c x))))))]
    [`(list/c ,c* ...) (foldr (λ (ci acc) (.cons/c (go ci) acc)) .empty/c c*)]
    [`(nelistof ,c)
     (define x (variable-not-in c 'X))
     (define d (go c))
     (.cons/c d (.μ/c x (.or/c l (list .empty/c (.cons/c d (.x/c x))))))]
    [`(one-of/c ,v ...) (go `(or/c ,@(for/list ([vi v]) `(λ (♣) (equal? ♣ ,vi)))))]
    ;; FIXME: only if there's no variable with such name in scope
    [`(add1 ,e) (.@ '+ (list (go e) .one) l)]
    [`(sub1 ,e) (.@ '- (list (go e) .one) l)]
    [`(zero? ,e) (.@ '= (list (go e) .zero) l)]
    [`(positive? ,e) (.@ '> (list (go e) .zero) l)]
    [`(negative? ,e) (.@ '< (list (go e) .zero) l)]
    [`(unless ,p ,e) (.if (go p) (go e) .void)]

    ;; basic contract forms
    [`(->i ((,x ,dom) ...) (,res (,dep ...) ,rng))
     (unless (equal? x dep)
       (error '->i "Please specify full dependency ~a instead of ~a for now" x dep))
     (.λ/c (map go dom) (read-e syms l (bind xs x) rng) #f)]
    [`(-> ,cx ... ,cy)
     (.λ/c (map go cx) (read-e syms l (bind xs (make-list (length xs) '♣)) cy) #f)]
    [`(->* (,cx ...) #:rest ,cz ,cy)
     (.λ/c (append (map go cx) (list (go cz)))
           (read-e syms l (bind xs (make-list (+ 1 (length cx)) '♣)) cy)
           #t)]
    [`(struct/c ,t ,cs ...) (.struct/c t (map go cs))]
    [`(,(or 'μ/c 'mu/c) (,x) ,c) (.μ/c x (read-e syms l (bind-name xs x) c))]

    ;; other basic exp forms
    [`(if ,e1 ,e2 ,e3) (.if (go e1) (go e2) (go e3))]
    [`(amb ,e* ...) (amb (map go e*))]
    [`(,(or 'lambda 'λ) (,x ...) ,e) (.λ (length x) (read-e syms l (bind xs x) e) #f)]
    [(or '• 'OPQ) ((on-•!))]
    [`(quote ,x) (.b x)]
    [(or (? number? x) (? boolean? x) (? string? x)) (prim x)]
    [`(,f ,xs ...) (.@ (go f) (map go xs) l)]
    [(? symbol? s)
     (or (resolve-symbol s)
         (error 'Parser "Unknown symbol ~a in module ~a" s l))]))

(define (bind xs x)
  (match x
    [(? symbol? x) (cons x xs)]
    [(? list? zs) (for/fold ([xs xs]) ([z zs]) (bind xs z))]))

(define (bind-name xs x) (cons (list x) xs))

(define (var xs z)
  (let loop ([xs xs] [i 0])
    (match xs
      ['() #f]
      [(cons (list x′) xr) (if (eq? x′ z) (.x/c x′) (loop xr i))]
      [(cons (? symbol? x′) xr) (if (eq? x′ z) (.x i) (loop xr (+ 1 i)))])))

(define (gen-names t acs)
  (set-union {set t (gen-p t)} {for/set ([ac acs]) (gen-ac t ac)}))
(define (gen-ac t ac)
  (string->symbol (format "~a-~a" t ac)))
(define (gen-p t)
  (string->symbol (format "~a?" t)))
