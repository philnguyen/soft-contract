#lang racket/base

;; Convert a zo struct to a more readable string representation.

;; Uses predicates to guess which struct we have, then convert the known
;; fields to strings.
;; Printing a field recursively is potentially expensive,
;; so we wrap the computation in a thunk.
;; The macro `lcons` makes thunk creation a little prettier.
;; The function `format-spec` forces these thunks.

;; Documentation for zo structs is online:
;; http://docs.racket-lang.org/raco/decompile.html

(provide
 ;; (: zo->string (->* (zo) (#:deep? Boolean) String))
 ;; Return a string representation of a zo struct
 zo->string
 ;; (: zo->spec (-> zo Spec))
 ;; Return a list-of-strings representation of a zo struct.
 ;; The structure of the list mirrors the structure of the original zo struct.
 zo->spec
 Spec)

;; --- string specifications

(require racket/match
         (only-in racket/list   empty?)
         (only-in racket/string string-join)
         (for-syntax racket/base racket/syntax)
         "../base/typed-zo-structs.rkt")

;; -----------------------------------------------------------------------------

;; --- API functions

;; Convert any zo struct to a spec/c representation.
(define
  (zo->spec z)
  (define z* (try-spec z))
  (if z*
      z*
      (error (format "Cannot format unknown struct ~e" z))))

;; Convert any zo struct to a string.
;; First builds a spec, then forces the thunks in that spec to build a string.
;; If `deep` is `#f`, only formats the name of the struct `z`.
(define
  (zo->string z #:deep? [deep? #t])
  (format-spec deep? (zo->spec z)))

;; --- syntax: lazy cons to delay evaluation of tail

;; Introduces syntax (lcons a:any b:any).
;; Wraps second argument in a thunk.
(define-syntax (lcons stx)
  (syntax-case stx ()
    [(_)       (raise-syntax-error #f "[lcons] Expected two arguments.")]
    [(_ _)     (raise-syntax-error #f "[lcons] Expected two arguments.")]
    [(_ hd tl) #'(cons hd (lambda () tl))]))

;; --- dispatch tables

(define (try-spec z)
  (match z
   [(? compilation-top?) (compilation-top->spec z)]
   [(? prefix?) (prefix->spec z)]
   [(? global-bucket?) (global-bucket->spec z)]
   [(? module-variable?) (module-variable->spec z)]
   [(? stx?) (stx->spec z)]
   [(? form?) (form->spec z)]
   [(? expr?) (expr->spec z)]
   [(? stx-obj?) (stx-obj->spec z)]
   [(? wrap?) (wrap->spec z)]
   [(? module-shift?) (module-shift->spec z)]
   [(? scope?) (scope->spec z)]
   [(? multi-scope?) (multi-scope->spec z)]
   [(? binding?) (binding->spec z)]
   [(? all-from-module?) (all-from-module->spec z)]
   [(? provided?) (provided->spec z)]
   [x (error 'try-spec (format "unknown struct ~e" z))]
))
(define (form->spec z)
  (match z
   [(? def-values?) (def-values->spec z)]
   [(? def-syntaxes?) (def-syntaxes->spec z)]
   [(? seq-for-syntax?) (seq-for-syntax->spec z)]
   [(? req?) (req->spec z)]
   [(? seq?) (seq->spec z)]
   [(? splice?) (splice->spec z)]
   [(? inline-variant?) (inline-variant->spec z)]
   [(? mod?) (mod->spec z)]
   [(? expr?) (expr->spec z)]
   [x (error 'form (format "unknown struct ~e" z))]
))
(define (expr->spec z)
  (match z
   [(? lam?) (lam->spec z)]
   [(? closure?) (closure->spec z)]
   [(? case-lam?) (case-lam->spec z)]
   [(? let-one?) (let-one->spec z)]
   [(? let-void?) (let-void->spec z)]
   [(? install-value?) (install-value->spec z)]
   [(? let-rec?) (let-rec->spec z)]
   [(? boxenv?) (boxenv->spec z)]
   [(? localref?) (localref->spec z)]
   [(? toplevel?) (toplevel->spec z)]
   [(? topsyntax?) (topsyntax->spec z)]
   [(? application?) (application->spec z)]
   [(? branch?) (branch->spec z)]
   [(? with-cont-mark?) (with-cont-mark->spec z)]
   [(? beg0?) (beg0->spec z)]
   [(? varref?) (varref->spec z)]
   [(? assign?) (assign->spec z)]
   [(? apply-values?) (apply-values->spec z)]
   [(? with-immed-mark?) (with-immed-mark->spec z)]
   [(? primval?) (primval->spec z)]
   [x (error 'expr (format "unknown struct ~e" z))]
))
(define (binding->spec z)
  (match z
   [(? module-binding?) (module-binding->spec z)]
   [(? decoded-module-binding?) (decoded-module-binding->spec z)]
   [(? local-binding?) (local-binding->spec z)]
   [(? free-id=?-binding?) (free-id=?-binding->spec z)]
   [x 'binding (error (format "unknown struct ~e" z))]
))
;; --- private functions

(define
  (compilation-top->spec z)
  (list "compilation-top"
        (lcons "max-let-depth" (number->string     (compilation-top-max-let-depth z)))
        (lcons "binding-namess" (hash->string        (compilation-top-binding-namess z)))
        (lcons "prefix"        (prefix->spec      (compilation-top-prefix z)))
        (lcons "code"          (form-or-any->string (compilation-top-code z)))))

(define
  (prefix->spec z)
  (define (tl->spec tl)
    (match tl
      [(? module-variable?)
       (format-spec #f (module-variable->spec tl))]
      [(? global-bucket?)
       (format-spec #f (global-bucket->spec tl))]
      [(? symbol?)
       (symbol->string tl)]
      [#f "#f"]))
  (list "prefix"
        (lcons "num-lifts" (number->string                (prefix-num-lifts z)))
        (lcons "toplevels" (list->string      tl->spec  (prefix-toplevels z)))
        (lcons "stxs"      (listof-zo->string stx->spec (for/list  ([sx (prefix-stxs z)] #:when sx) sx)))
        (lcons "src-inspector-desc" (symbol->string (prefix-src-inspector-desc z)))))

(define
  (global-bucket->spec  z)
  (list "global-bucket"
        (lcons "name" (symbol->string (global-bucket-name z)))))

(define
  (module-variable->spec z)
  (define (constantness->spec cs)
    (cond [(symbol? cs)         (symbol->string         cs)]
          [(function-shape? cs) (function-shape->spec cs)]
          [(struct-shape? cs)   (struct-shape->spec   cs)]
          [else          "#f"]))
  (list "module-variable"
        (lcons "modidx"       (module-path-index->string (module-variable-modidx z)))
        (lcons "sym"          (symbol->string            (module-variable-sym z)))
        (lcons "pos"          (number->string            (module-variable-pos z)))
        (lcons "phase"        (number->string            (module-variable-phase z)))
        (lcons "constantness" (constantness->spec      (module-variable-constantness z)))))

(define
  (stx->spec z)
  (list "stx"
        (lcons "content" (stx-obj->spec (stx-content z)))))

(define
  (all-from-module->spec z)
  (list "all-from-module"
        (lcons "path"      (module-path-index->string (all-from-module-path z)))
        (lcons "phase"     (number-or-f->string (all-from-module-phase z)))
        (lcons "src-phase" (number-or-f->string (all-from-module-src-phase z)))
        (lcons "inspector-desc" (symbol->string (all-from-module-inspector-desc z)))
        (lcons "exceptions" (list->string symbol->string (all-from-module-exceptions z)))
        (lcons "prefix"    (symbol-or-f->string (all-from-module-prefix z)))))

;; --- form

(define
  (def-values->spec z)
  (define (toplevel-or-symbol->string tl)
    (match tl
      [(? toplevel?)
       (format-spec #f (toplevel->spec tl))]
      [(? symbol?)
       (symbol->string tl)]))
  (list "def-values"
        (lcons "ids" (list->string toplevel-or-symbol->string (def-values-ids z)))
        (lcons "rhs" (let ([rhs (def-values-rhs z)])
                       (cond [(inline-variant? rhs) (inline-variant->spec rhs)]
                             [else (expr-seq-any->string rhs)])))))

(define
  (def-syntaxes->spec z)
  (define (toplevel-or-symbol->string tl)
    (match tl
      [(? toplevel?)
       (format-spec #f (toplevel->spec tl))]
      [(? symbol?)
       (symbol->string tl)]))
  (list "def-syntaxes"
        (lcons "ids"           (list->string toplevel-or-symbol->string (def-syntaxes-ids z)))
        (lcons "rhs"           (expr-seq-any->string                    (def-syntaxes-rhs z)))
        (lcons "prefix"        (prefix->spec                            (def-syntaxes-prefix z)))
        (lcons "max-let-depth" (number->string                          (def-syntaxes-max-let-depth z)))
        (lcons "dummy"         (toplevel-or-any->string                 (def-syntaxes-dummy z)))))

(define
  (seq-for-syntax->spec z)
  (list "seq-for-syntax"
        (lcons "forms"         (listof-form-or-any->string (seq-for-syntax-forms z)))
        (lcons "prefix"        (prefix->spec             (seq-for-syntax-prefix z)))
        (lcons "max-let-depth" (number->string             (seq-for-syntax-max-let-depth z)))
        (lcons "dummy"         (toplevel-or-any->string    (seq-for-syntax-dummy z)))))

(define
  (req->spec z)
  (list "req"
        (lcons "reqs"  (stx->spec      (req-reqs z)))
        (lcons "dummy" (toplevel->spec (req-dummy z)))))

(define
  (seq->spec z)
  (list "seq"
        (lcons "forms" (listof-form-or-any->string (seq-forms z)))))

(define
  (splice->spec z)
  (list "splice"
        (lcons "forms" (listof-form-or-any->string (splice-forms z)))))

(define
  (inline-variant->spec z)
  (list "inline-variant"
        (lcons "direct" (expr->spec (inline-variant-direct z)))
        (lcons "inline" (expr->spec (inline-variant-inline z)))))

(define
  (mod->spec z)
  (define (name->spec nm)
    (match nm
      [(? list?)
       (list->string  symbol->string nm)]
      [(? symbol?)
       (symbol->string nm)]))
  (define (unexported->spec ux)
    (define (elem->spec e)
      (format-list
       #:sep " "
       (list (number->string              (car e))
             (list->string symbol->string (cadr e))
             (list->string symbol->string (caddr e)))))
    (list->string elem->spec ux))
  (define (lang-info->spec li)
    (match li
      [(vector mp sym any)
        (format-list
         #:sep " "
         (list (module-path->spec mp)
               (symbol->string    sym)
               (any->string       any)))]
      [#f "#f"]))
  (define
    (provides->spec pds)
    (define (elem->spec e)
      (format-list
       #:sep " "
       (list (if (number? (car e))
                 (number->string (car e))
                 "#f")
             (listof-zo->string provided->spec (cadr e))
             (listof-zo->string provided->spec (caddr e)))))
    (list->string elem->spec pds))
  (define
    (requires->spec rqs)
    (define (elem->spec e)
      (format-list
       #:sep " "
       (list (if (number? (car e))
                 (number->string (car e))
                 "#f")
             (list->string module-path-index->string (cdr e)))))
    (list->string elem->spec rqs))
  (define
    (syntax-bodies->spec sbs)
    (define (ds-or-sfs->spec d)
      (cond [(def-syntaxes?   d) (format-spec #f (def-syntaxes->spec d))]
            [(seq-for-syntax? d) (format-spec #f (seq-for-syntax->spec d))]))
    (define (elem->spec e)
      (format-list
       #:sep " "
       (list (number->string                 (car e))
             (list->string ds-or-sfs->spec (cdr e)))))
    (list->string elem->spec sbs))
  (define (internal-context->string ic)
    (match ic
      [(? stx? ic)
       (stx->spec ic)]
      [(? vector? ic)
       (listof-zo->string stx->spec (vector->list ic))]
      [(? boolean? ic)
       (boolean->string ic)]))
  (list "mod"
        (lcons "name"             (name->spec               (mod-name z)))
        (lcons "srcname"          (symbol->string             (mod-srcname z)))
        (lcons "self-modidx"      (module-path-index->string  (mod-self-modidx z)))
        (lcons "prefix"           (prefix->spec             (mod-prefix z)))
        (lcons "provides"         (provides->spec       (mod-provides z)))
        (lcons "requires"         (requires->spec       (mod-requires z)))
        (lcons "body"             (listof-form-or-any->string (mod-body z)))
        (lcons "syntax-bodies"    (syntax-bodies->spec  (mod-syntax-bodies z)))
        (lcons "unexported"       (unexported->spec         (mod-unexported z)))
        (lcons "max-let-depth"    (number->string             (mod-max-let-depth z)))
        (lcons "dummy"            (toplevel->spec           (mod-dummy z)))
        (lcons "lang-info"        (lang-info->spec          (mod-lang-info z)))
        (lcons "internal-context" (internal-context->string (mod-internal-context z)))
        (lcons "binding-names"    (format "~a" (mod-binding-names z)))
        (lcons "flags"            (list->string   symbol->string (mod-flags z)))
        (lcons "pre-submodules"   (listof-zo->string mod->spec (mod-pre-submodules z)))
        (lcons "post-submodules"  (listof-zo->string mod->spec (mod-post-submodules z)))))

(define
  (provided->spec z)
  (define (mpi-or-f->string x)
    (if (eq? #f x)
        "#f"
        (module-path-index->string x)))
  (list "provided"
        (lcons "name"      (symbol->string (provided-name z)))
        (lcons "src"       (mpi-or-f->string (provided-src  z)))
        (lcons "src-name"  (symbol->string (provided-src-name z)))
        (lcons "nom-src"   (any->string (provided-nom-src z)))
        (lcons "src-phase" (number->string (provided-src-phase z)))
        (lcons "protected?" (boolean->string (provided-protected? z)))))

;; --- expr

;; Helper for `lam` and `case-lam`.
(define (lam-name->spec nm)
  (match nm
    [(? vector?)
     (any->string nm)]
    [(? empty?)
     "()"]
    [(? symbol?)
     (symbol->string nm)]))

(define
  (lam->spec z)
  (define (closure-map->spec cm)
    (list->string number->string (vector->list cm)))
  (define (toplevel-map->spec tm)
    (cond [(eq? #f tm) "#f"]
          [else (format-list
                 #:sep " "
                 (for/list ([n tm]) (number->string n)))]))
  (list "lam"
        (lcons "name"          (lam-name->spec                  (lam-name z)))
        (lcons "flags"         (list->string symbol->string (lam-flags z)))
        (lcons "num-params"    (number->string              (lam-num-params z)))
        (lcons "param-types"   (list->string symbol->string (lam-param-types z)))
        (lcons "rest?"         (boolean->string             (lam-rest? z)))
        (lcons "closure-map"   (closure-map->spec           (lam-closure-map z)))
        (lcons "closure-types" (list->string symbol->string (lam-closure-types z)))
        (lcons "toplevel-map"  (toplevel-map->spec          (lam-toplevel-map z)))
        (lcons "max-let-depth" (number->string              (lam-max-let-depth z)))
        (lcons "body"          (expr-seq-any->string        (lam-body z)))))

(define
  (closure->spec z)
  (list "closure"
        (lcons "code"   (lam->spec    (closure-code z)))
        (lcons "gen-id" (symbol->string (closure-gen-id z)))))

(define
  (case-lam->spec z)
  (list "case-lam"
        (lcons "name"    (lam-name->spec              (case-lam-name z)))
        (lcons "clauses" (list->string (lambda (x) (format-spec #f (expr->spec x))) (case-lam-clauses z)))))

(define
  (let-one->spec z)
  (list "let-one"
        (lcons "rhs"    (expr-seq-any->string (let-one-rhs  z)))
        (lcons "body"   (expr-seq-any->string (let-one-body z)))
        (lcons "type"   (symbol-or-f->string  (let-one-type z)))
        (lcons "unused?" (boolean->string      (let-one-unused? z)))))

(define
  (let-void->spec z)
  (list "let-void"
        (lcons "count" (number->string       (let-void-count z)))
        (lcons "boxes" (boolean->string      (let-void-boxes? z)))
        (lcons "body"  (expr-seq-any->string (let-void-body z)))))

(define
  (install-value->spec z)
  (list "install-value"
        (lcons "count"  (number->string       (install-value-count z)))
        (lcons "pos"    (number->string       (install-value-pos z)))
        (lcons "boxes?" (boolean->string      (install-value-boxes? z)))
        (lcons "rhs"    (expr-seq-any->string (install-value-rhs z)))
        (lcons "body"   (expr-seq-any->string (install-value-body z)))))

(define
  (let-rec->spec z)
  (list "let-rec"
        (lcons "procs" (list->string (lambda (lm ) (format-spec #f (lam->spec lm))) (let-rec-procs z)))
        (lcons "body"  (expr-seq-any->string          (let-rec-body z)))))

(define
  (boxenv->spec z)
  (list "boxenv"
        (lcons "pos"  (number->string       (boxenv-pos z)))
        (lcons "body" (expr-seq-any->string (boxenv-body z)))))

(define
  (localref->spec z)
  (list "localref"
        (lcons "unbox?"        (boolean->string     (localref-unbox? z)))
        (lcons "pos"           (number->string      (localref-pos z)))
        (lcons "clear?"        (boolean->string     (localref-clear? z)))
        (lcons "other-clears?" (boolean->string     (localref-other-clears? z)))
        (lcons "type"          (symbol-or-f->string (localref-type z)))))

(define
  (toplevel->spec z)
  (list
        "toplevel"
        (lcons "depth"  (number->string  (toplevel-depth z)))
        (lcons "pos"    (number->string  (toplevel-pos z)))
        (lcons "const?" (boolean->string (toplevel-const? z)))
        (lcons "ready?" (boolean->string (toplevel-ready? z)))))

(define
  (topsyntax->spec z)
  (list "topsyntax"
        (lcons "depth" (number->string (topsyntax-depth z)))
        (lcons "pos"   (number->string (topsyntax-pos z)))
        (lcons "midpt" (number->string (topsyntax-midpt z)))))

(define
  (application->spec z)
  (list "application"
        (lcons "rator" (expr-seq-any->string              (application-rator z)))
        (lcons "rands" (list->string expr-seq-any->string (application-rands z)))))

(define
  (branch->spec z)
  (list "branch"
        (lcons "test" (expr-seq-any->string (branch-test z)))
        (lcons "then" (expr-seq-any->string (branch-then z)))
        (lcons "else" (expr-seq-any->string (branch-else z)))))

(define
  (with-cont-mark->spec z)
  (list "with-cont-mark"
        (lcons "key"  (expr-seq-any->string (with-cont-mark-key  z)))
        (lcons "val"  (expr-seq-any->string (with-cont-mark-val  z)))
        (lcons "body" (expr-seq-any->string (with-cont-mark-body z)))))

(define
  (beg0->spec z)
  (list "beg0"
        (lcons "seq" (list->string expr-seq-any->string (beg0-seq z)))))

(define
  (varref->spec z)
  (list "varref"
        (lcons "toplevel" (match (varref-toplevel z)
                            [(? toplevel? tl) (toplevel->spec tl)]
                            [#t    "#t"]))
        (lcons "dummy"    (match (varref-dummy z)
                            [(? toplevel? dm) (toplevel->spec dm)]
                            [#f "#f"]))))

(define
  (assign->spec z)
  (list "assign"
        (lcons "id"        (toplevel->spec     (assign-id z)))
        (lcons "rhs"       (expr-seq-any->string (assign-rhs z)))
        (lcons "undef-ok?" (boolean->string      (assign-undef-ok? z)))))

(define
  (apply-values->spec z)
  (list "apply-values"
        (lcons "proc"      (expr-seq-any->string (apply-values-proc z)))
        (lcons "args-expr" (expr-seq-any->string (apply-values-args-expr z)))))

(define
  (with-immed-mark->spec z)
  (list "with-immed-mark"
        (lcons "key" (expr-seq-any->string (with-immed-mark-key z)))
        (lcons "def-val" (expr-seq-any->string (with-immed-mark-def-val z)))
        (lcons "body" (expr-seq-any->string (with-immed-mark-body z)))))

(define
  (primval->spec z)
  (list "primval"
        (lcons "id" (number->string (primval-id z)))))

;; --- stx-obj

(define
  (stx-obj->spec so)
  (list "stx-obj"
        (lcons "datum" (any->string (stx-obj-datum so)))
        (lcons "wrap" (wrap->spec (stx-obj-wrap so)))
        (lcons "srcloc" (srcloc->string (stx-obj-srcloc so)))
        (lcons "props" (hash->string (stx-obj-props so)))
        (lcons "tamper-status" (symbol->string (stx-obj-tamper-status so)))))

;; --- wrap

(define
  (wrap->spec wp)
  (define (ms->string ms+id)
    (format "(~a ~a)" (format-spec #f (multi-scope->spec (car ms+id)))
                      (number-or-f->string (cadr ms+id))))
  (list "wrap"
        (lcons "shifts" (listof-zo->string module-shift->spec (wrap-shifts wp)))
        (lcons "simple-scopes" (listof-zo->string scope->spec (wrap-simple-scopes wp)))
        (lcons "multi-scopes" (list->string ms->string (wrap-multi-scopes wp)))))

;; --- misc. syntax

(define
  (module-shift->spec ms)
  (list "module-shift"
        (lcons "from" (cond [(module-shift-from ms) => module-path-index->string] [else "#f"]))
        (lcons "to" (cond [(module-shift-to ms) => module-path-index->string] [else "#f"]))
        (lcons "from-inspector-desc" (symbol-or-f->string (module-shift-from-inspector-desc ms)))
        (lcons "to-inspector-desc" (symbol-or-f->string (module-shift-to-inspector-desc ms)))))

(define
  (scope->spec sc)
  (define (sym+scope+binding->string ssbs)
    (format "(~a ~a ~a)" (symbol->string (car ssbs))
                         (listof-zo->string scope->spec (cadr ssbs))
                         (format-spec #f (binding->spec (caddr ssbs)))))
  (define (scope+all-from-module->string bbs)
    (format "(~a ~a)" (listof-zo->string scope->spec (car bbs))
                      (format-spec #f (all-from-module->spec (cadr bbs)))))
  (list "scope"
        (lcons "name" (let ([name  (scope-name sc)])
                        (cond [(eq? 'root name) "root"]
                              [else (number->string name)])))
        (lcons "kind" (symbol->string (scope-kind sc)))
        (lcons "bindings" (list->string sym+scope+binding->string (scope-bindings sc)))
        (lcons "bulk-bindings" (list->string scope+all-from-module->string (scope-bulk-bindings sc)))
        (lcons "multi-owner" (cond [(scope-multi-owner sc) => multi-scope->spec]
                                   [else "#f"]))))

(define
  (multi-scope->spec ms)
  (define (sc->string id+scope)
    (format "(~a ~a)" (number-or-f->string (car id+scope))
                      (format-spec #f (scope->spec (cadr id+scope)))))
  (list "multi-scope"
        (lcons "name" (number->string (multi-scope-name ms)))
        (lcons "src-name" (any->string (multi-scope-src-name ms)))
        (lcons "scopes" (list->string sc->string (multi-scope-scopes ms)))))

;; --- binding

(define
  (module-binding->spec mb)
  (list "module-binding"
        (lcons "encoded" (any->string (module-binding-encoded mb)))))

(define
  (decoded-module-binding->spec dmb)
  (list "decoded-module-binding"
        (lcons "path" (cond [(decoded-module-binding-path dmb) => module-path-index->string] [else "#f"]))
        (lcons "name" (symbol->string (decoded-module-binding-name dmb)))
        (lcons "phase" (number->string (decoded-module-binding-phase dmb)))
        (lcons "nominal-path" (cond [(decoded-module-binding-nominal-path dmb) => module-path-index->string] [else "#f"]))
        (lcons "nominal-export-name" (symbol->string (decoded-module-binding-nominal-export-name dmb)))
        (lcons "nominal-phase" (number-or-f->string (decoded-module-binding-nominal-phase dmb)))
        (lcons "import-phase" (number-or-f->string (decoded-module-binding-import-phase dmb)))
        (lcons "inspector-desc" (symbol-or-f->string (decoded-module-binding-inspector-desc dmb)))))

(define
  (local-binding->spec lb)
  (list "local-binding"
        (lcons "name" (symbol->string (local-binding-name lb)))))

(define
  (free-id=?-binding->spec fib)
  (list "free-id=?-binding"
        (lcons "base" (binding->spec (free-id=?-binding-base fib)))
        (lcons "id" (stx-obj->spec (free-id=?-binding-id fib)))
        (lcons "phase" (number-or-f->string (free-id=?-binding-phase fib)))))

;; --- Shapes

;; Shapes are not zo structs per se, but they are documented in the
;; decompile guide and do not seem to have a nice formatting method.

(define
  (function-shape->spec fs)
  (format-list #:sep " "
               (list "function-shape"
                     (format "arity : ~a"            (function-shape-arity fs))
                     (format "preserves-marks? : ~a" (function-shape-preserves-marks? fs)))))

(define
  (struct-shape->spec ss)
  (cond [(struct-type-shape?  ss) (struct-type-shape->spec  ss)]
        [(constructor-shape?  ss) (constructor-shape->spec  ss)]
        [(predicate-shape?    ss) (predicate-shape->spec    ss)]
        [(accessor-shape?     ss) (accessor-shape->spec     ss)]
        [(mutator-shape?      ss) (mutator-shape->spec      ss)]
        [(struct-other-shape? ss) (struct-other-shape->spec ss)]
        [else (error (format "unknown struct shape ~a" ss))]))

(define
  (struct-type-shape->spec sts)
  (format-list #:sep " "
               (list "struct-type-shape"
                     (format "field-count : ~a" (struct-type-shape-field-count sts)))))

(define
  (constructor-shape->spec cs)
  (format-list #:sep " "
               (list "constructor-shape"
                     (format "arity : ~a" (constructor-shape-arity cs)))))

(define
  (predicate-shape->spec ps)
  (format-list (list "predicate-shape")))

(define
  (accessor-shape->spec sts)
  (format-list #:sep " "
               (list "accessor-shape"
                     (format "field-count : ~a" (accessor-shape-field-count sts)))))

(define
  (mutator-shape->spec sts)
  (format-list #:sep " "
               (list "mutator-shape"
                     (format "field-count : ~a" (mutator-shape-field-count sts)))))

(define
  (struct-other-shape->spec ps)
  (format-list (list "struct-other-shape")))

;; --- helpers

;; Turn any value into a string.
(define
  (any->string z)
  (format "~a" z))

;; Turn a boolean value into a string.
(define
  (boolean->string b)
  (any->string b))

;; Turn an 'expr' struct or a 'seq' struct or any other value into a string.
(define
  (expr-seq-any->string z)
  (cond [(expr? z) (format-spec #f (expr->spec z))]
        [(seq?  z) (format-spec #f (seq->spec z))]
        [else      (any->string z)]))

;; Turn a 'form' struct or anything else into a string.
(define
  (form-or-any->string fm)
  (cond [(form? fm) (format-spec #f (form->spec fm))]
        [else       (any->string   fm)]))

;; Alternate syntax for `string-join` -- the `sep` argument appears as a label
;; and defaults to a newline character.
(define
  (format-list xs #:sep [sep "\n"])
  (string-join xs sep))

;; Turn a spec into a string.
;; If `deep?` is false, only format the title (ignore the field names + thunks).
(define
  (format-spec deep? struct-spec)
  (define fields (cdr struct-spec))
  (define title (format "<struct:~a>" (car struct-spec)))
  (define field-name-lengths
    (for/list ([fd fields]) (string-length (car fd))))
  (define w ;; width of longest struct field name
    (if (empty? fields) 0 (apply max field-name-lengths)))
  (if (not deep?)
      title
      (format-list
       (cons title
             (for/list  ([fd  fields])
               (define forced ((cdr fd)))
               (define rest   (if (string? forced)
                                  forced
                                  (format-spec #f forced)))
               (format "  ~a : ~a" (pad (car fd) w) rest))))))

;; Turn a list into a string.
(define
  (list->string f xs)
  (format "[~a]"
          (format-list #:sep " "
                       (for/list  ([x  xs]) (f x)))))

;; Turn a list of things that might be 'form' structs into a list of strings.
(define
  (listof-form-or-any->string xs)
  (list->string form-or-any->string xs))

;; Turn a list of zo structs into a list of strings using the helper function
;; `z->spec`.
;; TODO should not be polymorphic -- want to bind to subtypes
(define
  (listof-zo->string z->spec zs)
  (cond [(empty? zs) "[]"]
        [else        (format "~a[~a]" (format-spec #f (z->spec (car zs))) (length zs))]))

;; Turn a module-path-index into a string
;; TODO I think we can do better than ~a
;; http://docs.racket-lang.org/reference/Module_Names_and_Loading.html
(define
  (module-path-index->string mpi)
  (any->string mpi))

;; Turn a module path into a string
;; TODO can probably improve on ~a
(define
  (module-path->spec mp)
  (any->string mp))

;; Turn a number or #f into a string.
(define
  (number-or-f->string nf)
  (if (eq? #f nf)
      "#f"
      (number->string nf)))

;; Turn a symbol or #f into a string.
(define
  (symbol-or-f->string sf)
  (if (eq? #f sf)
      "#f"
      (symbol->string sf)))

(define
  (hash->string h)
  (format "~a" h))


;; Turn something that might be a 'toplevel' struct into a string.
(define
  (toplevel-or-any->string tl)
  (cond [(toplevel? tl) (format-spec #f (toplevel->spec tl))]
        [else           (any->string tl)]))

;; --- misc

;; If `str` has fewer than `w` characters,
;; append `(w - (len str))` characters to its right end.
(define
  (pad str w #:char [c #\space])
  (define l (string-length str))
  (cond [(< l w) (format "~a~a" str (make-string (- w l) c))]
        [else    str]))
