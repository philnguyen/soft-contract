#lang racket
(require (only-in redex variable-not-in)
         "lang.rkt"
         "syntax.rkt")
(provide
 #;(combine-out read-p read-e gen-ac gen-p opaque)
 (contract-out
  [read-p (any/c . -> . p?)]
  [read-e (any/c . -> . p?)]
  [gen-ac (symbol? symbol? . -> . symbol?)]
  [gen-p (symbol? . -> . symbol?)]
  [opaque (any/c . -> . any/c)]))

(define (read-p prog)
  (define abbrevs (make-hash))
  (match prog
    [`((abbrev/c ,from ,to) ... ,ms ... (require ,main-reqs ...) ,e)
     (for ([from/c from] [to/c to]) (hash-set! abbrevs from/c to/c))
     (let-values ([(all outs reqs) ; first pass, read provides and requires
                   (for/fold
                       ([all (hash '† ∅)] [outs (hash '† ∅)] [reqs (hash '† (list->set main-reqs))]) ([m ms])
                     (match m
                       [`(module ,l ,ds ...)
                        (for/fold
                            ([all (hash-set all l ∅)]
                             [outs (hash-set outs l ∅)]
                             [reqs (hash-set reqs l ∅)]) ([d ds])
                          (match d
                            ; remember requires
                            [`(require ,x ...)
                             (values all outs [hash-update reqs l (λ (s) (set-union s (list->set x)))])]
                            ; remember provides
                            [`(provide ,provs ...)
                             (values all
                                     [for/fold ([outs outs]) ([prov provs])
                                       (match prov
                                         [`(struct ,t ([,fields ,_] ...))
                                          (hash-update outs l (λ (s) (set-union s (gen-names t fields))))]
                                         [`(,x ,_)
                                          (hash-update outs l (λ (s) (set-add s x)))])]
                                     reqs)]
                            ; remember (possibly local) value bindings
                            [(or `(,[or 'define 'define*] (,f ,_ ...) ,_) `(define ,[? symbol? f] ,_))
                             (values [hash-update all l (λ (s) (set-add s f))] outs reqs)]
                            ; remember generated struct names
                            [`(struct ,t (,fields ...))
                             (values [hash-update all l (λ (s) (set-union s (gen-names t fields)))]
                                     outs reqs)]))]))])
       
       (define (read-m l ds)
         (let-values ([(decs defs)
                       (for/fold ([decs (hash)] [defs (hash)]) ([d ds])
                         (match d ; TODO handle struct as macros
                           [`(provide ,provs ...)
                            (values (for/fold ([decs decs]) ([prov provs])
                                      (match prov
                                        [`(struct ,t ([,field ,c] ...))
                                         (let* ([field-cs (map (curry read-c l '() '()) c)]
                                                [strct-c (struct-c t field-cs)])
                                           (for/fold ([decs (hash-set* decs
                                                                       t (func-c field-cs strct-c #f)
                                                                       (gen-p t) pred-c)])
                                             ([field-name field] [field-c field-cs])
                                             (hash-set decs (gen-ac t field-name) (func-c (list strct-c) field-c #f))))]
                                        [`(,x ,c) (hash-set decs x (read-c l '() '() c))]))
                                    defs)]
                           [`(define* (,f ,x ... ,z) ,e)
                            (values decs (hash-set defs f (read-e l '() `(λ* (,@ x ,z) ,e))))]
                           [`(define (,f ,x ...) ,e)
                            (values decs (hash-set defs f (read-e l '() `(λ ,x ,e))))]
                           [`(define ,x ,v) (values decs (hash-set defs x (read-e l '() v)))]
                           [`(struct ,t (,names ...))
                            (let ([n (length names)])
                              (values decs
                                      (let loop ([defs (hash-set* defs t (struct-mk t n) (gen-p t) (struct-p t n))]
                                                 [i 0] [fields names])
                                        (match fields
                                          ['() defs]
                                          [(cons field fields′) (loop [hash-set defs (gen-ac t field) (struct-ac t n i)] [add1 i] fields′)]))))]
                           [_ (values decs defs)]))])
           (m decs defs)))
       
       (define (resolve-ref from x)
         (if (or [set-member? (hash-ref all from) x]
                 [set-member? (hash-ref outs from) x])
             (ref from from x)
             (for/first ([to (hash-ref reqs from)]
                         #:when (set-member? (hash-ref outs to) x))
               (ref from to x))))
       
       (define (read-c l xs xcs c)
         (define go (curry read-c l xs xcs))
         (match c
           [`(and/c ,c1 ,c2) (and-c [go c1] [go c2])]
           [`(or/c ,c1 ,c2) (or-c [go c1] [go c2])]
           [`(cons/c ,c1 ,c2) (struct-c 'cons (list [go c1] [go c2]))]
           [`(μ ,x ,c′) (μ-c x (read-c l xs (cons x xcs) c′))]
           [`(listof ,c1) (go `(μ X (or/c empty? (cons/c ,c1 X))))]
           [`(nelistof ,c1) (go `(cons/c ,c1 (μ X (or/c empty? (cons/c ,c1 X)))))]
           [`(-> [,x : ,cx] ... ,cy)
            (func-c (map go cx) (read-c l (push x xs) xcs cy) #f)]
           [`(-> ,cx ... ,cy) (go `(-> ,@ (map (λ (c) `[☠ : ,c]) cx) ,cy))]
           [`(->* [,x : ,cx] ... [,z : ,cz] ,cy)
            (func-c (append [map go cx] [list (go cz)])
                    (read-c l (cons z (push x xs)) xcs cy) #t)]
           [`(->* ,cx ... ,cy) (go `(->* ,@ (map (λ (c) `[☠ : ,c]) cx) ,cy))]
           [`(struct/c ,t ,cs) (struct-c t (map go cs))]
           [`(one-of/c ,v) (read-c l xs xcs `(λ (♦) (equal? ♦ ,v)))]
           [`(one-of/c ,v1 ,vi ...) (or-c (read-c l xs xcs `(λ (♦) (equal? ♦ ,v1)))
                                          (read-c l xs xcs `(one-of/c ,@ vi)))]
           [(? symbol? z)
            (cond
              [(hash-has-key? abbrevs z) (go (hash-ref abbrevs z))]
              [(member z xcs) z]
              [else (match (resolve-ref l z)
                      [(and (ref _ _ _) r) (f 1 (@ l r (list [x 0])) #f)]
                      [#f (match (prim z)
                            [#f (error (format "Parsing error: Unexpected symbol ~a" z))]
                            [o o])])])]
           [pred (read-e l xs pred)]))
       
       (define (read-e l xs e)
         (define go (curry read-e l xs))
         (match e
           ; syntactic sugar
           [`(and) #t]
           [`(and ,e′) (go e′)]
           [`(and ,e1 ,e′ ...) (if/ [go e1] [go `(and ,@ e′)] #f)]
           [`(or) #f]
           [`(or ,e′) (go e′)]
           [`(or ,e1 ,e′ ...)
            (let ([x (variable-not-in e′ 'tmp)])
              (go `(let [,x ,e1]
                     (if ,x ,x (or ,@ e′)))))]
           [`(begin ,e′) (go e′)]
           [`(begin ,e1 ,e′ ...)
            (let ([x (variable-not-in e′ '_)])
              (go `(let [,x ,e1] (begin ,@ e′))))]
           [`(cond [else ,e′]) (go e′)]
           [`(cond [,e1 ,e2] ,p ...) (go `(if ,e1 ,e2 (cond ,@ p)))]
           [`(let ([,x ,ex] ...) ,e) (go `((λ ,x ,e) ,@ ex))]
           [`(let [,x ,ex] ,e) (go `((λ (,x) ,e) ,ex))]
           [`(let* ([,x ,ex]) ,e) (go `((λ (,x) ,e) ,ex))]
           [`(let* ([,x ,ex] ,p ...) ,e) (go `(let [,x ,ex] (let* ,p ,e)))]
           
           ; real language constructs
           [`(if ,e1 ,e2 ,e3) (if/ [go e1] [go e2] [go e3])]
           [`(amb ,es ...) (amb (map go es))]
           [`(,[or 'lambda 'λ] (,x ...) ,e′) (f [length x] [read-e l (push x xs) e′] #f)]
           [`(,[or 'lambda* 'λ*] (,x ... ,var) ,e′)
            (f [add1 (length x)] [read-e l (cons var (push x xs)) e′] #t)]
           [`• (•)]
           [`(quote ,x) x]
           [`(,func ,args ...) (@ l [go func] [map go args])]
           [(or [? number? x] [? boolean? x] [? string? x]) x]
           [(? symbol? s)
            (match (index-of s xs)
              [(? number? i) (x i)]
              [#f (match (resolve-ref l s)
                    [(and (ref _ _ _) r) r]
                    [#f (match (prim s)
                          [#f (error (format "Parsing error: Unexpected symbol ~a in module ~a" s l))]
                          [o o])])])]
           [weird (error "Parsing error: Invalid expression syntax" weird)]))
       
       ; read each module
       (with-havoc (p
                    (for/fold ([mods (hash)]) ([m ms])
                      (match-let ([`(module ,l ,ds ...) m])
                        (hash-set mods l (read-m l ds))))
                    (read-e '† '() e))))]
    [`(,ms ... ,e) (read-p `(,@ ms (require) ,e))]))

(define (read-e e)
  (read-p (list e)))

;; opaque : S-exp -> S-exp
(define opaque
  (match-lambda
    [`(module ,name ,d ...)
     `(module ,name ,@ (for/fold ([ds '()]) ([di d])
                         (match di
                           [`(define ,_ ...) ds]
                           [`(provide ,decs ...)
                            (cons di
                                  (for/fold ([ds ds]) ([dec decs])
                                    (match dec
                                      [`(struct ,t ([,f ,_] ...))
                                       (for/fold ([ds ds]) ([name (gen-names t f)])
                                         (cons `(define ,name •) ds))]
                                      [`(,x ,_) (cons `(define ,x •) ds)])))]
                           [`(require ,_ ...) (cons di ds)])))]))



;(: push ([Listof Symbol] → [Listof Symbol]))
(define (push zs xs)
  (foldl cons xs zs))

;(: index-of (Symbol [Listof Symbol] → Int))
(define (index-of x xs)
  (for/first ([xi xs] [i (in-naturals)] #:when (equal? x xi)) i))

(define (gen-ac t a)
  (string->symbol (string-append (symbol->string t) "-" (symbol->string a))))
(define (gen-p t)
  (string->symbol (string-append (symbol->string t) "?")))

(define (gen-names t fs)
  (list->set `(,t ,(gen-p t) ,@ (map (curry gen-ac t) fs))))

(define pred-c (func-c (list [op 'any]) (op 'bool?) #f))