#lang racket/base

;; Access the fields of a struct by name at runtime.

;; Uses predicates to guess what struct its argument is,
;; then compares strings with statically-known field names.
;; Functions that end with '->' are the specific transition function
;; for a type of zo struct.

(provide
 ;; (-> zo? string? (values (or/c zo? (listof zo?)) boolean?))
 ;; Access "structName-fieldName myStruct" at runtime.
 zo-transition)

(require compiler/zo-structs
         racket/match
         (only-in racket/list empty? empty))

;; -----------------------------------------------------------------------------

;; --- API functions

;; Look up the field name `field-name` in the struct `z`.
;; First use predicates to decide what type of struct `z` is,
;; then use string equality to check if `field-name` matches any
;; statically-known name.
;; Return two values.
;; - First is a zo struct or list of zo structs, depending on the
;;   value stored in the field denoted by `field-name`
;; - Second is a boolean indicating success or failure.
;;   On failure, the returned zo struct is `z`.
(define (zo-transition z field-name)
  ;; (-> zo? string? (values (or/c zo? (listof zo?)) boolean?))
  ;; Check if transition failed or returned a list without any zo, pack result values.
  (match (try-transition z field-name)
    [(? zo? nxt)
     (values nxt #t)]
    [(? list? nxt)
     (match (filter zo? nxt)
       ['() (values z #f)]
       [zs  (values zs #t)])]
    [_
     (values z #f)]))

;; --- dispatch

(define (try-transition z str)
  (match z
   [(? compilation-top?) (compilation-top-> z str)]
   [(? prefix?) (prefix-> z str)]
   [(? global-bucket?) (global-bucket-> z str)]
   [(? module-variable?) (module-variable-> z str)]
   [(? stx?) (stx-> z str)]
   [(? form?) (form-> z str)]
   [(? wrapped?) (wrapped-> z str)]
   [(? wrap?) (wrap-> z str)]
   [(? free-id-info?) (free-id-info-> z str)]
   [(? all-from-module?) (all-from-module-> z str)]
   [(? module-binding?) (module-binding-> z str)]
   [(? nominal-path?) (nominal-path-> z str)]
   [(? provided?) (provided-> z str)]
   [x #f]
))
(define (form-> z str)
  (match z
   [(? def-values?) (def-values-> z str)]
   [(? def-syntaxes?) (def-syntaxes-> z str)]
   [(? seq-for-syntax?) (seq-for-syntax-> z str)]
   [(? req?) (req-> z str)]
   [(? seq?) (seq-> z str)]
   [(? splice?) (splice-> z str)]
   [(? inline-variant?) (inline-variant-> z str)]
   [(? mod?) (mod-> z str)]
   [(? provided?) (provided-> z str)]
   [(? expr?) (expr-> z str)]
   [x #f]
))
(define (expr-> z str)
  (match z
   [(? lam?) (lam-> z str)]
   [(? closure?) (closure-> z str)]
   [(? case-lam?) (case-lam-> z str)]
   [(? let-one?) (let-one-> z str)]
   [(? let-void?) (let-void-> z str)]
   [(? install-value?) (install-value-> z str)]
   [(? let-rec?) (let-rec-> z str)]
   [(? boxenv?) (boxenv-> z str)]
   [(? localref?) (localref-> z str)]
   [(? toplevel?) (toplevel-> z str)]
   [(? topsyntax?) (topsyntax-> z str)]
   [(? application?) (application-> z str)]
   [(? branch?) (branch-> z str)]
   [(? with-cont-mark?) (with-cont-mark-> z str)]
   [(? beg0?) (beg0-> z str)]
   [(? varref?) (varref-> z str)]
   [(? assign?) (assign-> z str)]
   [(? apply-values?) (apply-values-> z str)]
   [(? primval?) (primval-> z str)]
   [x #f]
))
(define (wrap-> z str)
  (match z
   [(? top-level-rename?) (top-level-rename-> z str)]
   [(? mark-barrier?) (mark-barrier-> z str)]
   [(? lexical-rename?) (lexical-rename-> z str)]
   [(? phase-shift?) (phase-shift-> z str)]
   [(? module-rename?) (module-rename-> z str)]
   [(? wrap-mark?) (wrap-mark-> z str)]
   [(? prune?) (prune-> z str)]
   [x #f]
))
(define (module-binding-> z str)
  (match z
   [(? simple-module-binding?) (simple-module-binding-> z str)]
   [(? phased-module-binding?) (phased-module-binding-> z str)]
   [(? exported-nominal-module-binding?) (exported-nominal-module-binding-> z str)]
   [(? nominal-module-binding?) (nominal-module-binding-> z str)]
   [(? exported-module-binding?) (exported-module-binding-> z str)]
   [x #f]
))
(define (nominal-path-> z str)
  (match z
   [(? simple-nominal-path?) (simple-nominal-path-> z str)]
   [(? imported-nominal-path?) (imported-nominal-path-> z str)]
   [(? phased-nominal-path?) (phased-nominal-path-> z str)]
   [x #f]
))
;; --- getters

(define (compilation-top-> z field-name)
  ;; (-> compilation-top? string? (or/c (listof zo?) zo? #f))
  (match field-name
    ["prefix"
     (compilation-top-prefix z)]
    ["code"
     (compilation-top-code   z)]
    [_ #f]))

(define (prefix-> z field-name)
  ;; (-> prefix? string? (or/c (listof zo?) zo? #f))
  (define (gb-or-mv? tl)
    (or (global-bucket? tl) (module-variable? tl)))
  (match field-name
    ["toplevels"
     (filter gb-or-mv? (prefix-toplevels z))]
    ["stxs"
     (prefix-stxs z)]
    [_ #f]))

(define (global-bucket-> z field-name)
  ;; (-> global-bucket? string? (or/c (listof zo?) zo? #f))
  #f)

(define (module-variable-> z field-name)
  ;; (-> module-variable? string? (or/c (listof zo?) zo? #f))
  #f)

(define (stx-> z field-name)
  ;; (-> stx? string? (or/c (listof zo?) zo? #f))
  (match field-name
    ["encoded"
     (stx-encoded z)]
    [_  #f]))

(define (wrapped-> z field-name)
  ;; (-> wrapped? string? (or/c (listof zo?) zo? #f))
  (match field-name
    ["wraps"
     (wrapped-wraps z)]
    [_ #f]))

(define (free-id-info-> z field-name)
  ;; (-> free-id-info? string? (or/c (listof zo?) zo? #f))
  #f)

(define (all-from-module-> z field-name)
 ;; (-> all-from-module? string? (or/c (listof zo?) zo? #f))
  #f)

;; --- form

(define (def-values-> z field-name)
  ;; (-> def-values? string? (or/c (listof zo?) zo? #f))
  (match field-name
    ["ids"
     (filter toplevel? (def-values-ids z))]
    ["rhs"
     (match (def-values-rhs z)
       [(or (? expr? rhs) (? seq? rhs) (? inline-variant? rhs))
        rhs]
       [_ #f])]
  [_ #f]))

(define (def-syntaxes-> z field-name)
  ;; (-> def-syntaxes? string? (or/c (listof zo?) zo? #f))
  (match field-name
    ["ids"
     (filter toplevel? (def-syntaxes-ids z))]
    ["rhs"
     (match (def-syntaxes-rhs z)
       [(or (? expr? rhs) (? seq? rhs)) rhs]
       [_ #f])]
    ["prefix"
     (def-syntaxes-prefix z)]
    ["dummy"
     (match (def-syntaxes-dummy z)
       [(? toplevel? dm) dm]
       [_ #f])]
    [_ #f]))

(define (seq-for-syntax-> z field-name)
  ;; (-> seq-for-syntax? string? (or/c (listof zo?) zo? #f))
  (match field-name
    ["forms"
     (filter form? (seq-for-syntax-forms z))]
    ["prefix"
     (seq-for-syntax-prefix z)]
    ["dummy"
     (match (seq-for-syntax-dummy z)
       [(? toplevel? dm) dm]
       [_ #f])]
    [_ #f]))

(define (req-> z field-name)
  ;; (-> req? string? (or/c (listof zo?) zo? #f))
  (match field-name
    ["reqs"
     (req-reqs z)]
    ["dummy"
     (req-dummy z)]
    [_ #f]))

(define (seq-> z field-name)
  ;; (-> seq? string? (or/c (listof zo?) zo? #f))
  (match field-name
    ["forms"
     (filter form? (seq-forms z))]
    [_ #f]))

(define (splice-> z field-name)
  ;; (-> splice? string? (or/c (listof zo?) zo? #f))
  (match field-name
    ["forms"
     (filter form? (splice-forms z))]
    [_ #f]))

(define (inline-variant-> z field-name)
  ;; (-> inline-variant? string? (or/c (listof zo?) zo? #f))
  (match field-name
    ["direct"
     (inline-variant-direct z)]
    ["inline"
     (inline-variant-inline z)]
    [_ #f]))

(define (mod-> z field-name)
  ;; (-> mod? string? (or/c (listof zo?) zo? #f))
  (define (get-provided pds)
    ;; (-> (listof (list/c (or/c exact-integer? #f) (listof provided?) (listof provided?))) (listof provided?))
    (cond [(empty? pds) empty]
          [else (append (cadar pds)
                        (caddar pds)
                        (get-provided (cdr pds)))]))
  (define (get-syntaxes sxs)
    ;; (-> (listof (cons/c exact-positive-integer? (listof (or/c def-syntaxes? seq-for-syntax?)))) (listof (or/c def-syntaxes? seq-for-syntax?)))
    (cond [(empty? sxs) empty]
          [else (append (cdar sxs)
                        (get-syntaxes (cdr sxs)))]))
  (match field-name
    ["prefix"
     (mod-prefix z)]
    ["provides"
     (get-provided (mod-provides z))]
    ["body"
     (filter form? (mod-body z))]
    ["syntax-bodies"
     (get-syntaxes (mod-syntax-bodies z))]
    ["dummy"
     (mod-dummy z)]
    ["internal-context"
     (match (mod-internal-context z)
       [(? stx? ic) ic]
       [(? vector? ic) (vector->list ic)]
       [_ #f])]
    ["pre-submodules"
     (mod-pre-submodules z)]
    ["post-submodules"
     (mod-post-submodules z)]
    [_ #f]))

(define (provided-> z field-name)
  ;; (-> provided? string? (or/c (listof zo?) zo? #f))
  #f)

;; --- expr

(define (lam-> z field-name)
  ;; (-> lam? string? (or/c (listof zo?) zo? #f))
  (match field-name
    ["body"
     (match (lam-body z)
       [(? expr-or-seq? bd) bd]
       [_x #f])]
    [_ #f]))

(define (closure-> z field-name)
  ;; (-> closure? string? (or/c (listof zo?) zo? #f))
  (match field-name
    ["code"
     (closure-code z)]
    [_ #f]))

(define (case-lam-> z field-name)
  ;; (-> case-lam? string? (or/c (listof zo?) zo? #f))
  (match field-name
    ["clauses"
     (case-lam-clauses z)]
    [_ #f]))

(define (let-one-> z field-name)
  ;; (-> let-one? string? (or/c (listof zo?) zo? #f))
  (match field-name
    ["rhs"
     (match (let-one-rhs z)
       [(? expr-or-seq? rhs) rhs]
       [_ #f])]
    ["body"
     (match (let-one-body z)
       [(? expr-or-seq? body) body]
       [_ #f])]
    [_ #f]))

(define (let-void-> z field-name)
  ;; (-> let-void? string? (or/c (listof zo?) zo? #f))
  (match field-name
    ["body"
     (match (let-void-body z)
       [(? expr-or-seq? body) body]
       [_ #f])]
    [_ #f]))

(define (install-value-> z field-name)
  ;; (-> install-value? string? (or/c (listof zo?) zo? #f))
  (match field-name
    ["rhs"
     (match (install-value-rhs z)
       [(? expr-or-seq? rhs) rhs]
       [_ #f])]
    ["body"
     (match (install-value-body z)
       [(? expr-or-seq? body) body]
       [_ #f])]
    [_ #f]))

(define (let-rec-> z field-name)
  ;; (-> let-rec? string? (or/c (listof zo?) zo? #f))
  (match field-name
    ["procs"
     (let-rec-procs z)]
    ["body"
     (match (let-rec-body z)
       [(? expr-or-seq? body) body]
       [_ #f])]
    [_ #f]))

(define (boxenv-> z field-name)
  ;; (-> boxenv? string? (or/c (listof zo?) zo? #f))
  (match field-name
    ["body"
     (match (boxenv-body z)
       [(? expr-or-seq? body) body]
       [_ #f])]
    [_ #f]))

(define (localref-> z field-name)
  ;; (-> localref? string? (or/c (listof zo?) zo? #f))
  #f)

(define (toplevel-> z field-name)
  ;; (-> toplevel? string? (or/c (listof zo?) zo? #f))
  #f)

(define (topsyntax-> z field-name)
  ;; (-> topsyntax? string? (or/c (listof zo?) zo? #f))
  #f)

(define (application-> z field-name)
  ;; (-> application? string? (or/c (listof zo?) zo? #f))
  (match field-name
    ["rator"
     (match (application-rator z)
       [(? expr-or-seq? rator) rator]
       [_ #f])]
    ["rands"
     (filter expr-or-seq? (application-rands z))]
    [_ #f]))

(define (branch-> z field-name)
  ;; (-> branch? string? (or/c (listof zo?) zo? #f))
  (match field-name
    ["test"
     (match (branch-test z)
       [(? expr-or-seq? test) test]
       [_ #f])]
    ["then"
     (match (branch-then z)
       [(? expr-or-seq? then) then]
       [_ #f])]
    ["else"
     (match (branch-else z)
       [(? expr-or-seq? el) el]
       [_ #f])]
    [_ #f]))

(define (with-cont-mark-> z field-name)
  ;; (-> with-cont-mark? string? (or/c (listof zo?) zo? #f))
  (match field-name
    ["key"
     (match (with-cont-mark-key z)
       [(? expr-or-seq? key)  key]
       [_ #f])]
    ["val"
     (match (with-cont-mark-val z)
       [(? expr-or-seq? val) val]
       [_ #f])]
    ["body"
     (match (with-cont-mark-body z)
       [(? expr-or-seq? body) body]
       [_ #f])]
    [_ #f]))

(define (beg0-> z field-name)
  ;; (-> beg0? string? (or/c (listof zo?) zo? #f))
  (match field-name
    ["seq" (filter expr-or-seq? (beg0-seq z))]
    [_ #f]))

(define (varref-> z field-name)
  ;; (-> varref? string? (or/c (listof zo?) zo? #f))
  (match field-name
    ["toplevel"
     (match (varref-toplevel z)
       [(? toplevel? tl) tl]
       [_ #f])]
    ["dummy"
     (match (varref-dummy z)
       [(? toplevel? dm) dm]
       [_ #f])]
    [_ #f]))

(define (assign-> z field-name)
  ;; (-> assign? string? (or/c (listof zo?) zo? #f))
  (match field-name
    ["id" (assign-id z)]
    ["rhs" (match (assign-rhs z)
             [(? expr-or-seq? rhs) rhs]
             [_ #f])]
    [_ #f]))

(define (apply-values-> z field-name)
  ;; (-> apply-values? string? (or/c (listof zo?) zo? #f))
  (match field-name
    ["proc"
     (match (apply-values-proc z)
       [(? expr-or-seq? proc) proc]
       [_ #f])]
    ["args-expr"
     (match (apply-values-args-expr z)
       [(? expr-or-seq? args-expr) args-expr]
       [_ #f])]
    [_ #f]))

(define (primval-> z field-name)
  ;; (-> primval? string? (or/c (listof zo?) zo? #f))
  #f)

;; --- wrap

(define (top-level-rename-> z field-name)
  ;; (-> top-level-rename? string? (or/c (listof zo?) zo? #f))
  #f)

(define (mark-barrier-> z field-name)
  ;; (-> mark-barrier? string? (or/c (listof zo?) zo? #f))
  #f)

(define (lexical-rename-> z field-name)
  ;; (-> lexical-rename? string? (or/c (listof zo?) zo? #f))
  (define (get-free-id-info als)
    ;; (-> (listof (cons/c symbol? (or/c symbol? (cons/c symbol? (or/c (cons/c symbol? (or/c symbol? #f)) free-id-info?))))) (listof free-id-info?))
    (for/list ([blah als]
               #:when (and (pair? (cdr blah))
                           (free-id-info? (cddr blah))))
      (cddr blah)))
  (match field-name
    ["alist"
     (get-free-id-info (lexical-rename-alist z))]
    [_ #f]))
  
(define (phase-shift-> z field-name)
  ;; (-> phase-shift? string? (or/c (listof zo?) zo? #f))
  #f)

(define (module-rename-> z field-name)
  ;; (-> module-rename? string? (or/c (listof zo?) zo? #f))
  (match field-name
    ["unmarshals" (module-rename-unmarshals z)]
    ["renames"    (for/list ([mbpair (module-rename-renames z)]) (cdr mbpair))]
    [_ #f]))

(define (wrap-mark-> z field-name)
  ;; (-> wrap-mark? string? (or/c (listof zo?) zo? #f))
  #f)

(define (prune-> z field-name)
  ;; (-> prune? string? (or/c (listof zo?) zo? #f))
  #f)

;; --- module-binding

(define (simple-module-binding-> z field-name)
  ;; (-> simple-module-binding? string? (or/c (listof zo?) zo? #f))
  #f)

(define (phased-module-binding-> z field-name)
  ;; (-> phased-module-binding? string? (or/c (listof zo?) zo? #f))
  (match field-name
    ["nominal-path" (phased-module-binding-nominal-path z)]
    [_ #f]))

(define (exported-nominal-module-binding-> z field-name)
  ;; (-> exported-nominal-module-binding? string? (or/c (listof zo?) zo? #f))
  (match field-name
    ["nominal-path" (exported-nominal-module-binding-nominal-path z)]
    [_ #f]))

(define (nominal-module-binding-> z field-name)
  ;; (-> nominal-module-binding? string? (or/c (listof zo?) zo? #f))
  (match field-name
    ["nominal-path" (nominal-module-binding-nominal-path z)]
    [_ #f]))

(define (exported-module-binding-> z field-name)
  ;; (-> exported-module-binding? string? (or/c (listof zo?) zo? #f))
  #f)

;; --- nominal-path

(define (simple-nominal-path-> z field-name)
  ;; (-> simple-nominal-path? string? (or/c (listof zo?) zo? #f))
  #f)

(define (imported-nominal-path-> z field-name)
  ;; (-> imported-nominal-path? string? (or/c (listof zo?) zo? #f))
  #f)

(define (phased-nominal-path-> z field-name)
  ;; (-> phased-nominal-path? string? (or/c (listof zo?) zo? #f))
  #f)

;; --- helpers

;; True if the argument is an 'expr' or a 'seq' zo struct.
(define (expr-or-seq? x)
  ;; (-> any/c boolean?)
  (or (expr? x) (seq? x)))

