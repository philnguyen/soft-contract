#lang racket/base

(require racket/dict
         racket/list
         racket/path
         racket/port
         syntax/id-table
         syntax/parse
         unstable/hash
         racket/contract/private/provide)

(provide scv-ignore?)

(define (flatten* l)
  (if l (flatten l) null))

(define (scv-ignore? stx)
  (or (syntax-property stx 'scv:ignore)
      (memf (λ (i) (eq? (syntax-e i) 'handle-contract-out)) (flatten* (syntax-property stx 'origin)))
      (syntax-parse stx #:literals (define-values #%plain-app vector)
        [(define-values (_:id)
           (#%plain-app (~datum do-partial-app) _ _ _ _ (#%plain-app vector . _)))
         #t]
        [_ #f])))

(provide do-expand)

(define (identifier-binding* i)
  (if (dict-ref lexical-bindings i #f)
      'lexical
      (identifier-binding i)))

(define (hash-set* h . kvs)
  (let loop ([kvs kvs] [h h])
    (if (null? kvs)
        h
        (let* ([k (car kvs)]
               [v (cadr kvs)]
               [h (if v (hash-set h k v) h)])
          (loop (cddr kvs) h)))))

(define (hash* . kvs) (apply hash-set* (hash) kvs))


(define lexical-bindings (make-free-id-table))

(define (register-all! x)
  (cond [(list? x) (for-each register-all! x)]
        [(identifier? x) (dict-set! lexical-bindings x #t)]
        [(pair? x)
         (register-all! (car x))
         (register-all! (cdr x))]
        [(syntax? x) (register-all! (syntax-e x))]
        [else (error 'register-all! "unexpected ~a" x)]))

(define (do-expand stx)
  ;; error checking
  (syntax-parse stx #:literals ()
    [((~and mod-datum (~datum module)) n:id lang:expr . rest)
     (void)]
    [((~and mod-datum (~datum module)) . rest)
     (error 'do-expand "got ill-formed module: ~a\n" (syntax->datum #'rest))]
    [rest
     (error 'do-expand "got something that isn't a module: ~a\n" (syntax->datum #'rest))])
  ;; work
  (parameterize ([current-namespace (make-base-namespace)])
    (namespace-syntax-introduce (expand stx))))

(define current-module (make-parameter #f))

(define (index->path i)
  (define-values (v _) (module-path-index-split i))
  (if v
      (list (resolved-module-path-name (module-path-index-resolve i)) #f)
      (list (current-module) #t)))


(define keep-srcloc (make-parameter #t))

(define table (make-free-id-table))
(define sym-table (make-hash))

(define (gen-name id)
  ;; use strings to make sure unreadablility isn't an issue
  (if (hash-ref sym-table (symbol->string (syntax-e id)) #f)
      (gensym (syntax-e id))
      (begin (hash-set! sym-table (symbol->string (syntax-e id)) #t)
             (syntax-e id))))

(define quoted? (make-parameter #f))

(define (id->sym id)
  (define sym (identifier-binding-symbol id))
  (define sym*
    (if (eq? 'lexical (identifier-binding id))
        (dict-ref! table id (λ _
                               ;(printf ">>> miss: ~a\n" id)
                               (gen-name id)))
        sym))
  ;(printf ">>> id sym sym*: ~a ~a ~a\n" id sym sym*)
  (symbol->string
   (if (quoted?)
       (syntax-e id)
       sym*)))

(define-syntax-class provide-form
  (pattern
   ((~datum contract-out) [i:id c:expr] ...)
   #:attr contracts (map hash
                         (map syntax->datum (syntax->list #'(i ...)))
                         (map syntax->datum (syntax->list #'(c ...)))))
  [pattern _ #:attr contracts null])

(define-syntax-class mod-form
  (pattern
   ((~datum provide) p:provide-form ...)
   #:attr contracts (attribute p.contracts))
  (pattern
   ((~datum provide/contract) [i:id c:expr] ...)
   #:attr contracts (map hash
                         (map syntax->datum (syntax->list #'(i ...)))
                         (map syntax->datum (syntax->list #'(c ...)))))
  [pattern _ #:attr contracts null])

(define (find-contracts m)
  (syntax-parse m
    [(module m lang form:mod-form ...)
     (apply hash-union (flatten (attribute form.contracts)))]))

(provide do-expand-toplevel)
;; given a string which should be a sequence of modules, fully-expand
;; them all as if they were in a `racket/load` context
(define (do-expand-toplevel str)
  (define p (open-input-string str))
  (define stxs (port->list (lambda (p) (read-syntax 'toplevel p)) p))
  (parameterize ([current-namespace (make-base-namespace)])
    (for/list ([m stxs])
      (syntax-parse m
        [((~datum module) . _) (void)]
        [_ (error 'do-expand-toplevel "expected a module")])
      (define cnts (find-contracts m))
      (define m* (namespace-syntax-introduce (expand m)))
      (eval-syntax m*)
      (list (syntax->datum m*) cnts))))

(provide do-expand-file)

(define (do-expand-file in)
  
  (define input (if (input-port? in) in (open-input-file in)))
  ;; If the given input is a file name, then chdir to its containing
  ;; directory so the expand function works properly
  (define in-path (if (input-port? in) #f (normalize-path in)))
  (unless (input-port? in)
    (define in-dir (or (path-only in) "."))
    (current-module (object-name input))
    (current-directory in-dir))
  (read-accept-reader #t)
  (read-accept-lang #t)
  
  (define stx (read-syntax (object-name input) input))
  (do-expand stx))


;; example use
(module+ main
  (do-expand (read-syntax #f (open-input-string "(module m racket 5)"))))
