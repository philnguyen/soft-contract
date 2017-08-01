#lang typed/racket/base

(provide (all-defined-out))

(require racket/match
         "../ast/definition.rkt"
         "../main.rkt")

(define-type Count (HashTable Symbol Natural))

(: make-counter : → (Values Count (Symbol * → Void)))
(define (make-counter)
  (define m : Count (make-hasheq))
  (values m
          (λ ks
            (for ([k ks])
              (hash-update! m k add1 (λ () 0))))))

(define-type Stx (Rec X (U -top-level-form
                           -e
                           -general-top-level-form
                           -e
                           -module
                           -begin/top
                           -module-level-form
                           (Listof X))))

(: count-checks : Stx → Count)
;; Return a static estimation of run-time checks.
;; Numbers are conservative in that we only count up checks that definitely need to be there
(define (count-checks stx)

  (define-values (stats up!) (make-counter))

  (: go! : Stx → Void)
  (define (go! stx)
    (match stx
      [(? list? es) (for-each go! es)]
      
      [(-provide specs)
       (for ([spec specs])
         (match-define (-p/c-item _ c _) spec)
         (c.go! c))]
      [(-define-values _ e) (up! 'values) (go! e)]
      
      [(-λ _ e) (go! e)] ; don't count arity check here
      [(-case-λ clauses)
       (for ([clause clauses]) (go! (cdr clause)))]

      [(-x _ _) (up! #;'undefined)]
      [(-@ f xs _)
       (up! 'procedure? 'arity 'values) (go! f)
       (for ([x xs]) (up! 'values) (go! x))
       ;; TODO: count up for each non-total primitive appearing in `f`.
       (match f
         [(or (? -st-ac?) (? -st-mut?)) (up! 'partial)]
         [(? symbol? o) #:when (hash-has-key? partial-prims o) (up! 'partial)]
         [_ (void)])]
      [(-if i t e) (up! 'values) (go! i) (go! t) (go! e)]
      [(-wcm k v e) (go! k) (go! v) (go! e)]
      [(-begin es) (for-each go! es)]
      [(-begin0 e es) (go! e) (for-each go! es)]
      [(or (-let-values bindings e _)
           (-letrec-values bindings e _))
       (for ([binding (in-list bindings)])
         (up! 'values)
         (go! (cdr binding)))
       (go! e)]
      [(-set! _ e) (up! 'values) (go! e)]

      ;; Switch to `c.go!` mode for contracts
      [(and c (or (? -μ/c?) (? -->?)) (? -->i?) (? -case->?) (? -struct/c?))
       (c.go! c)]

      [(-module _ body) (for-each go! body)]
      ;; FIXME count up for primitives
      [_
       (log-warning "conservatively not counting checks for ~a~n" stx)
       (void)]))

  (: c.go! : -e → Void)
  ;; Mostly similar to `go!`, but count up every value at leaves of contracts
  (define (c.go! c)
    (up! 'values 'contract?)
    (match c
      [(-μ/c _ c*) (c.go! c*)]
      [(--> dom rng _)
       (match dom
         [(-var cs c) (for-each c.go! cs) (c.go! c)]
         [(? list? cs) (for-each c.go! cs)])
       (c.go! rng)
       (up! 'procedure? 'arity)]
      [(-->i dom rng _)
       (for-each c.go! dom) (c.go! rng)
       (up! 'procedure? 'arity)]
      [(-case-> clauses _)
       (for ([clause clauses])
         (match-define (cons cs d) clause)
         (for-each c.go! cs) (c.go! d))
       (up! 'procedure? 'arity)]
      [(-x/c _) (up! 'leaf)]
      [(-struct/c _ cs _) (for-each c.go! cs) (up! 'struct)]
      [(? -o? o) (up! 'leaf)]
      [(-@ (or 'and/c 'or/c 'not/c) cs _) (for-each c.go! cs)]
      ;; Switch to `go!` for expressions
      [e (go! e) (up! 'leaf)]))

  (go! stx)
  (let ([total (apply + (hash-values stats))])
    (hash-set! stats 'total total)
    stats))
