#lang racket/base
(require racket/match racket/list racket/set
         "utils.rkt" "lang.rkt" (only-in redex/reduction-semantics variable-not-in))
(provide read-p on-•!)

(define on-•! (make-parameter (λ () '•)))

;; figure out define/provide/require for each module
(define (pass-1 p)
  (match p
    [`(,m* ... (require (quote ,main-reqs) ...) ,e)
     (for/fold ([M (hash '† (list ∅ ∅ (list->set main-reqs)))]) ([m m*])
       (match m
         [`(module ,name racket ,d* ...)
          (hash-set
           M
           name
           (for/fold ([acc (list ∅ ∅ ∅)]) ([d d*])
             (match-let ([(list defs decs reqs) acc])
               (match d
                 [`(require (submod ".." ,x*) ...) (list defs decs (set-union reqs (list->set x*)))]
                 [`(provide/contract ,prov* ...)
                  (list defs
                        (for/fold ([decs decs]) ([prov prov*])
                          (match prov
                            [`(struct ,t ([,field* ,_] ...)) (set-union decs (gen-names t field*))]
                            [`(,(? sym? x) ,_) (set-add decs x)]
                            [_ (error 'Parser "Expect provide clause as one of:~n (name contract)~n (struct struct-name ([field-name contract] …))~n.Given:~n~a"
                                      (pretty prov))]))
                        reqs)]
                 [(or `(,(or 'define 'define*) (,f ,_ ...) ,_) `(define ,f ,_))
                  (list (set-add defs f) decs reqs)]
                 [`(struct ,t (,field* ...))
                  (list (set-union defs (gen-names t field*)) decs reqs)]
                 [_ (error 'Parser "Expect one of:~n (require (submod \"..\" module-name) …)~n (provide/contract (x c) …)~n (define x v)~n (struct name (field …))~n.Given:~n~a" (pretty d))]))))]
         [_ (error 'Parser "Expect module definition of the form~n (module module-name racket _ …)~n.Given:~n~a" (pretty m))]))]
    [`(,_ ... ,(and req `(require ,_ ...)) ,_)
     (error 'Parser "Expect require clause of form (require 'name …)~nGiven:~n ~a" req)]
    [`(,m* ... ,e) (pass-1 `(,@ m* (require) ,e))]))

;; read and return program's ast
(define (read-p p)
  #;(printf "~a~n~n" p)
  (match p
    [`((module ,l* racket ,d** ...) ... (require ,_ ...) ,e)
     (define syms (pass-1 p))
     (define ms (for/hash ([l l*] [d* d**]) (values l (read-m syms l d*))))
     (define accs (gen-accs (hash-values ms)))
     (.p (.m* l* ms) accs (read-e syms '† '() e))]
    [`(,(and m `(module ,_ racket ,_ ...)) ... ,e) (read-p `(,@m (require) ,e))]
    [_ (error 'Parser "Invalid program form. Expect~n((module module-name racket~n (provide/contract [x c] …)~n (require (submod \"..\" module-name) …)~n (define x v) …) …).~nGiven:~n~a"
              (pretty p))]))

(define h∅ (hash))

;; read and return module's ast
(define (read-m syms l ds)
  (let*-values (; read each provide/define clause
                [(decs defs rev-order)
                 (for/fold ([decs h∅] [defs h∅] [order empty]) ([d ds])
                   (match d
                     [`(provide/contract ,prov* ...)
                      (values (for/fold ([decs decs]) ([prov prov*])
                                (match prov
                                  [`(struct ,t ([,field* ,c*] ...))
                                   (let* ([field-cs (for/list ([c c*]) (read-e syms l '() c))]
                                          [strct-c (.struct/c t field-cs)])
                                     (for/fold ([decs (hash-set*
                                                       decs
                                                       t (.λ/c field-cs strct-c #f)
                                                       (gen-p t) .any/c #;.pred/c)])
                                       ([field field*] [field-c field-cs])
                                       (hash-set decs (gen-ac t field) (.λ/c (list strct-c) field-c #f))))]
                                  [`(,x ,c) (hash-set decs x (read-e syms l '() c))]))
                              defs order)]
                     [`(define* (,f ,x ... ,z) ,e)
                      (values decs (hash-set defs f (read-e syms l '() `(λ* (,@x ,z) ,e))) (cons f order))]
                     [`(define (,f ,x ...) ,e)
                      (values decs (hash-set defs f (read-e syms l '() `(λ ,x ,e))) (cons f order))]
                     [`(define ,x ,v) (values decs (hash-set defs x (read-e syms l '() v)) (cons x order))]
                     [`(struct ,t (,field* ...))
                      (let ([n (length field*)])
                        (values decs
                                (for/fold ([defs (hash-set*
                                                  defs
                                                  t (.st-mk t n)
                                                  (gen-p t) (.st-p t n))])
                                  ([field field*] [i (in-naturals)])
                                  (hash-set defs (gen-ac t field) (.st-ac t n i)))
                                (append (for/list ([f field*]) (gen-ac t f))
                                        (list* (gen-p t) t order))))]
                     [_ (values decs defs order)]))]
                ; rebuild table from definitions
                [(m1) (for/hash ([(l e) (in-hash defs)])
                        (values l (cons e (hash-ref decs l #f))))]
                ; undefined but declared values are •
                [(m2 ro)
                 (for/fold ([m m1] [ro rev-order]) ([(l c) (in-hash decs)]
                                                    #:unless (hash-has-key? m1 l))
                   (values (hash-set m l (cons ((on-•!)) c)) (cons l ro)))])
    (.m (reverse ro) m2)))

(define (read-e syms l xs e)
  (define (go ei) (read-e syms l xs ei))
  ; assume ♣ never appears in source code
  (match e
    ;; syntactic sugar
    [`(and) .tt]
    [`(and ,e) (go e)]
    [`(and ,e1 ,er ...) (.if (go e1) (go `(and ,@er)) .ff)]
    [`(or) .ff]
    [`(or ,e) (go e)]
    [`(or ,e1 ,er ...) (go `(let [♣ ,e1]
                              (if ♣ ♣ (or ,@er))))]
    [`(implies ,e1 ,e2) (.if (go e1) (go e2) .tt)]
    [`(begin) (.b #f)] ; dummy
    [`(begin ,e) (go e)]
    [`(begin ,e* ...) (let ([n (length e*)])
                        (.@ (.λ n (.x 0) #f) (map go e*) l))]
    [`(cond [else ,e]) (go e)]
    [`(cond [,e1 ,e2] ,p ...) (.if (go e1) (go e2) (go `(cond ,@p)))]
    [`(let ([,x ,ex] ...) ,e) (go `((λ ,x ,e) ,@ex))]
    [`(let [,x ,ex] ,e) (go `((λ (,x) ,e) ,ex))]
    [`(let* () ,e) (go e)]
    [`(let* ([,x ,ex] ,p ...) ,e) (go `(let [,x ,ex] (let* ,p ,e)))]
    [`(list ,e* ...)
     (foldr (λ (ei acc) (.@ (prim 'cons) (list (go ei) acc) l)) (prim 'empty) e*)]
    [`(>=/c ,e) (go `(λ (♣) (>= ♣ ,e)))]
    [`(>/c ,e) (go `(λ (♣) (> ♣ ,e)))]
    [`(<=/c ,e) (go `(λ (♣) (<= ♣ ,e)))]
    [`(</c ,e) (go `(λ (♣) (< ♣ ,e)))]
    [`(=/c ,e) (go `(λ (♣) (= ♣ ,e)))]
    [`(and/c ,e* ...) (.and/c l (map go e*))]
    [`(or/c ,e* ...) (.or/c l (map go e*))]
    [`(not/c ,c) (.not/c l (go c))]
    [`(=>/c ,c ,d) (.or/c l (list (.not/c l (go c)) (go d)))]
    [`(cons/c ,c ,d) (.struct/c 'cons (list (go c) (go d)))]    
    [`(listof ,c)
     (let ([x (variable-not-in c 'X)])
       (.μ/c x (.or/c l (list .empty/c (.cons/c (go c) (.x/c x))))))]
    [`(list/c ,c* ...) (foldr (λ (ci acc) (.cons/c (go ci) acc)) .empty/c c*)]
    [`(nelistof ,c) (let ([x (variable-not-in c 'X)]
                          [d (go c)])
                      (.cons/c d (.μ/c x (.or/c l (list .empty/c (.cons/c d (.x/c x)))))))]
    [`(one-of/c ,v ...) (go `(or/c ,@(for/list ([vi v]) `(λ (♣) (equal? ♣ ,vi)))))]
    ; FIXME: only if there's no variable with such name in scope
    [`(add1 ,e) (.@ '+ (list (go e) .one) l)]
    [`(sub1 ,e) (.@ '- (list (go e) .one) l)]
    [`(zero? ,e) (.@ '= (list (go e) .zero) l)]
    [`(positive? ,e) (.@ '> (list (go e) .zero) l)]
    [`(negative? ,e) (.@ '< (list (go e) .zero) l)]
    [`(unless ,p ,e) (.if (go p) (go e) .void)]
    
    ;; basic contract forms
    #;[`(-> [,x : ,cx] ... ,cy) (.λ/c (map go cx) (read-e syms l (bind xs x) cy) #f)]
    [`(->i ((,x ,dom) ...) (,res (,dep ...) ,rng))
     (unless (equal? x dep)
       (error '->i "Please specify full dependency ~a instead of ~a for now" x dep))
     (.λ/c (map go dom) (read-e syms l (bind xs x) rng) #f)]
    [`(-> ,cx ... ,cy)
     (.λ/c (map go cx) (read-e syms l (bind xs (make-list (length xs) '♣)) cy) #f)
     #;(go `(->i
           ,(for/list ([c cx]) `(♣ ,c))
           (res ,(make-list (length cx) '♣) ,cy)))]
    #;[`(->* [,x : ,cx] ... [,z : ,cz] ,cy)
     (.λ/c (append (map go cx) (list (go cz)))
           (read-e syms l (bind (bind xs x) z) cy)
           #t)]
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
    #;[`(,(or 'lambda* 'λ*) (,x ... ,xn) ,e)
     (.λ (+ 1 (length x)) (read-e syms l (bind (bind xs x) xn) e) #t)]
    [(or '• 'OPQ) ((on-•!))]
    [`(quote ,x) (.b x)]
    [(or (? num? x) (? bool? x) (? str? x)) (prim x)]
    #;[`(apply ,f ,xs) (.apply (go f) (go xs) l)]
    [`(,f ,xs ...) (.@ (go f) (map go xs) l)]
    [(? sym? s)
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
                 ['negative? (.λ 1 (.@ '< (list (.x 0) .zero)) l) #f]
                 [_ #f])
               (error 'Parser "Unknown symbol ~a in module ~a" s l))))]))

(define (bind xs x)
  (match x
    [(? sym? x) (cons x xs)]
    [(? list? zs) (for/fold ([xs xs]) ([z zs]) (bind xs z))]))

(define (bind-name xs x) (cons (list x) xs))

(define (var xs z)
  (let loop ([xs xs] [i 0])
    (match xs
      ['() #f]
      [(cons (list x′) xr) (if (eq? x′ z) (.x/c x′) (loop xr i))]
      [(cons (? sym? x′) xr) (if (eq? x′ z) (.x i) (loop xr (+ 1 i)))])))

(define (gen-names t acs)
  (set-union {set t (gen-p t)} {for/set ([ac acs]) (gen-ac t ac)}))
(define (gen-ac t ac)
  (string->symbol (string-append (symbol->string t) "-" (symbol->string ac))))
(define (gen-p t)
  (string->symbol (string-append (symbol->string t) "?")))
