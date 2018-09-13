#lang typed/racket/base

(provide prims-zo@)

(require racket/match
         racket/contract
         racket/set
         
         compiler/decompile
         compiler/zo-parse
         compiler/zo-marshal
         compiler/zo-structs
         
         (except-in typed/racket/unit prefix)
         syntax/parse/define
         set-extras
         "../utils/debug.rkt"
         (except-in "../ast/signatures.rkt" normalize-arity arity-includes?)
         "signatures.rkt"
         "def.rkt"
         (for-syntax racket/base
                     racket/syntax
                     syntax/parse))

(define-unit prims-zo@
  (import prim-runtime^)
  (export)
  ;; FIXME: things seem to have changed with Racket 7.0
  #|
  ;;;;; 7.1 API for Decompiling
  (def decompile ((or/c linkl-directory? linkl-bundle? linkl?) . -> . any/c))

  ;;;;; 7.2 API for Parsing Bytecode
  (def zo-parse
    (case->
     [-> (or/c linkl-directory? linkl-bundle?)]
     [input-port? . -> . (or/c linkl-directory? linkl-bundle?)]))
  (def decode-module-binding (module-binding? symbol? . -> . decoded-module-binding?))

  ;;;;; 7.3 API for Marshalling Bytecode
  (def zo-marshal-to ((or/c linkl-directory? linkl-bundle?) output-port? . -> . void?))
  (def zo-marshal ((or/c linkl-directory? linkl-bundle?) . -> . bytes?))

  ;;;;; 7.4 Bytecode Representation
  (def-struct zo ()
    #:extra-constructor-name make-zo
    #:substructs
    (def-struct compilation-top ([max-let-depth exact-nonnegative-integer?]
                                 [binding-namess (hash/c exact-nonnegative-integer? (hash/c symbol? stx?))]
                                 [prefix prefix?]
                                 [code any/c])
      #:extra-constructor-name make-compilation-top)
    (def-struct prefix
      ([num-lifts exact-nonnegative-integer?]
       [toplevels (listof (or/c #f symbol? global-bucket? module-variable?))]
       [stxs (listof (or/c #f stx?))]
       [src-inspector-desc symbol?])
      #:extra-constructor-name make-prefix)
    (def-struct global-bucket ([name symbol?])
      #:extra-constructor-name make-global-bucket)
    (def-struct module-variable
      ([modidx module-path-index?]
       [sym symbol?]
       [pos exact-integer?]
       [phase exact-nonnegative-integer?]
       [constantness (or/c #f 'constant 'fixed function-shape? struct-shape?)])
      #:extra-constructor-name make-module-variable)
    (def-struct stx ([content stx-obj?]) #:extra-constructor-name make-stx)

    ;; 7.4.2 Forms
    (def-struct form ()
      #:extra-constructor-name make-form
      #:substructs
      (def-struct def-values ([ids (listof toplevel?)]
                              [rhs any/c])
        #:extra-constructor-name make-def-values)
      (def-struct def-syntaxes ([ids (listof symbol?)]
                                [rhs any/c]
                                [prefix prefix?]
                                [max-let-depth exact-nonnegative-integer?]
                                [dummy (or/c toplevel? #f)])
        #:extra-constructor-name make-def-syntaxes)
      (def-struct seq-for-syntax ([forms list?]
                                  [prefix prefix?]
                                  [max-let-depth exact-nonnegative-integer?]
                                  [dummy (or/c toplevel? #f)])
        #:extra-constructor-name make-seq-for-syntax)
      (def-struct req ([reqs stx?]
                       [dummy toplevel?])
        #:extra-constructor-name make-req)
      (def-struct seq ([forms list?])
        #:extra-constructor-name make-seq)
      (def-struct splice ([forms list?])
        #:extra-constructor-name make-splice)
      (def-struct inline-variant ([direct expr?]
                                  [inline expr?])
        #:extra-constructor-name make-inline-variant)
      (def-struct mod ([name (or/c symbol? (listof symbol?))]
                       [srcname symbol?]
                       [self-modidx module-path-index?]
                       [prefix prefix?]
                       [provides (listof (list/c (or/c exact-integer? #f)
                                                 (listof provided?)
                                                 (listof provided?)))]
                       [requires (listof (cons/c (or/c exact-integer? #f)
                                                 (listof module-path-index?)))]
                       [body list?]
                       [syntax-bodies (listof (cons/c exact-positive-integer?
                                                      (listof (or/c def-syntaxes? seq-for-syntax?))))]
                       [unexported (listof (list/c exact-nonnegative-integer?
                                                   (listof symbol?)
                                                   (listof symbol?)))]
                       [max-let-depth exact-nonnegative-integer?]
                       [dummy toplevel?]
                       [lang-info (or/c #f (vector/c module-path? symbol? any/c))]
                       [internal-context (or/c #f #t stx? (vectorof stx?))]
                       [binding-names (hash/c exact-integer? (hash/c symbol? (or/c #t stx?)))]
                       [flags (listof 'cross-phase)]
                       [pre-submodules (listof mod?)]
                       [post-submodules (listof mod?)])
        #:extra-constructor-name make-mod)
      
      ;; 7.4.3 Expressions
      (def-struct expr ()
        #:extra-constructor-name make-expr
        #:substructs
        (def-struct lam ([name (or/c symbol? vector?)]
                         [flags (listof (or/c 'preserves-marks 'is-method 'single-result
                                              'only-rest-arg-not-used 'sfs-clear-rest-args))]
                         [num-params exact-nonnegative-integer?]
                         [param-types (listof (or/c 'val 'ref 'flonum 'fixnum 'extflonum))]
                         [rest? boolean?]
                         [closure-map (vectorof exact-nonnegative-integer?)]
                         [closure-types (listof (or/c 'val/ref 'flonum 'fixnum 'extflonum))]
                         [toplevel-map (or/c #f (set/c exact-nonnegative-integer?))]
                         [max-let-depth exact-nonnegative-integer?]
                         [body any/c])
          #:extra-constructor-name make-lam)
        (def-struct closure ([code lam?]
                             [gen-id symbol?])
          #:extra-constructor-name make-closure)
        (def-struct case-lam ([name (or/c symbol? vector?)]
                              [clauses (listof lam?)])
          #:extra-constructor-name make-case-lam)
        (def-struct let-one ([rhs any/c]
                             [body any/c]
                             [type (or/c #f 'flonum 'fixnum 'extflonum)]
                             [unused? boolean?])
          #:extra-constructor-name make-let-one)
        (def-struct let-void ([count exact-nonnegative-integer?]
                              [boxes? boolean?]
                              [body any/c])
          #:extra-constructor-name make-let-void)
        (def-struct install-value ([count exact-nonnegative-integer?]
                                   [pos exact-nonnegative-integer?]
                                   [boxes? boolean?]
                                   [rhs any/c]
                                   [body any/c])
          #:extra-constructor-name make-install-value)
        (def-struct let-rec ([procs (listof lam?)]
                             [body any/c])
          #:extra-constructor-name make-let-rec)
        (def-struct boxenv ([pos exact-nonnegative-integer?]
                            [body any/c])
          #:extra-constructor-name make-boxenv)
        (def-struct localref ([unbox? boolean?]
                              [pos exact-nonnegative-integer?]
                              [clear? boolean?]
                              [other-clears? boolean?]
                              [type (or/c #f 'flonum 'fixnum 'extflonum)])
          #:extra-constructor-name make-localref)
        (def-struct toplevel ([depth exact-nonnegative-integer?]
                              [pos exact-nonnegative-integer?]
                              [const? boolean?]
                              [ready? boolean?])
          #:extra-constructor-name make-toplevel)
        (def-struct topsyntax ([depth exact-nonnegative-integer?]
                               [pos exact-nonnegative-integer?]
                               [midpt exact-nonnegative-integer?])
          #:extra-constructor-name make-topsyntax)
        (def-struct application ([rator any/c]
                                 [rands list?])
          #:extra-constructor-name make-application)
        (def-struct branch ([test any/c]
                            [then any/c]
                            [else any/c])
          #:extra-constructor-name make-branch)
        (def-struct with-cont-mark ([key any/c]
                                    [val any/c]
                                    [body any/c])
          #:extra-constructor-name make-with-cont-mark)
        (def-struct beg0 ([seq list?])
          #:extra-constructor-name make-beg0)
        (def-struct varref ([toplevel (or/c toplevel? #t)]
                            [dummy (or/c toplevel? #f)])
          #:extra-constructor-name make-varref)
        (def-struct assign ([id toplevel?]
                            [rhs any/c]
                            [undef-ok? boolean?])
          #:extra-constructor-name make-assign)
        (def-struct apply-values ([proc any/c]
                                  [args-expr any/c])
          #:extra-constructor-name make-apply-values)
        (def-struct with-immed-mark ([key any/c]
                                     [def-val any/c]
                                     [body any/c])
          #:extra-constructor-name make-with-immed-mark)
        (def-struct primval ([id exact-nonnegative-integer?])
          #:extra-constructor-name make-primval))
      )

    (def-struct provided ([name symbol?]
                          [src (or/c module-path-index? #f)]
                          [src-name symbol?]
                          [nom-src (or/c module-path-index? #f)]
                          [src-phase exact-nonnegative-integer?]
                          [protected? boolean?])
      #:extra-constructor-name make-provided)

    (def-struct stx-obj ([datum any/c]
                         [wrap wrap?]
                         [srcloc (or/c #f srcloc?)]
                         [props (hash/c symbol? any/c)]
                         [tamper-status (or/c 'clean 'armed 'tainted)])
      #:extra-constructor-name make-stx-obj)
    (def-struct wrap ([shifts (listof module-shift?)]
                      [simple-scopes (listof scope?)]
                      [multi-scopes (listof (list/c multi-scope? (or/c #f exact-integer?)))])
      #:extra-constructor-name make-wrap)
    (def-struct module-shift ([from (or/c #f module-path-index?)]
                              [to (or/c #f module-path-index?)]
                              [from-inspector-desc (or/c #f symbol?)]
                              [to-inspector-desc (or/c #f symbol?)])
      #:extra-constructor-name make-module-shift)
    (def-struct scope ([name (or/c 'root exact-nonnegative-integer?)]
                       [kind symbol?]
                       [bindings (listof (list/c symbol? (listof scope?) binding?))]
                       [bulk-bindings (listof (list/c (listof scope?) all-from-module?))]
                       [multi-owner (or/c #f multi-scope?)])
      #:extra-constructor-name make-scope)
    (def-struct multi-scope ([name exact-nonnegative-integer?]
                             [src-name any/c]
                             [scopes (listof (list/c (or/c #f exact-integer?) scope?))])
      #:extra-constructor-name make-multi-scope)
    (def-struct binding ()
      #:extra-constructor-name make-binding
      #:substructs
      (def-struct module-binding ([encoded any/c])
        #:extra-constructor-name make-module-binding)
      (def-struct decoded-module-binding ([path (or/c #f module-path-index?)]
                                          [name symbol?]
                                          [phase exact-integer?]
                                          [nominal-path (or/c #f module-path-index?)]
                                          [nominal-export-name symbol?]
                                          [nominal-phase (or/c #f exact-integer?)]
                                          [import-phase (or/c #f exact-integer?)]
                                          [inspector-desc (or/c #f exact-integer?)])
        #:extra-constructor-name make-decoded-module-binding)
      (def-struct local-binding ([name symbol?])
        #:extra-constructor-name make-local-binding)
      (def-struct free-id=?-binding ([base (and/c binding? (not/c free-id=?-binding?))]
                                     [id stx-obj?]
                                     [phase (or/c #f exact-integer?)])
        #:extra-constructor-name make-free-id=?-binding))
    (def-struct all-from-module ([path module-path-index?]
                                 [phase (or/c #f exact-integer?)]
                                 [src-phase (or/c #f exact-integer?)]
                                 [inspector-desc symbol?]
                                 [exceptions (listof symbol?)]
                                 [prefix (or/c symbol? #f)])
      #:extra-constructor-name make-all-from-module)
    )
  
  (def-struct function-shape
    ([arity procedure-arity?]
     [preserves-marks? boolean?])
    #:extra-constructor-name make-function-shape)

  (def-struct struct-shape ()
    #:extra-constructor-name make-struct-shape
    #:substructs
    (def-struct struct-type-shape ([field-count exact-nonnegative-integer?])
      #:extra-constructor-name make-struct-type-shape)
    (def-struct constructor-shape ([arity exact-nonnegative-integer?])
      #:extra-constructor-name make-constructor-shape)
    (def-struct predicate-shape ()
      #:extra-constructor-name make-predicate-shape)
    (def-struct accessor-shape ([field-count exact-nonnegative-integer?])
      #:extra-constructor-name make-accessor-shape)
    (def-struct mutator-shape ([field-count exact-nonnegative-integer?])
      #:extra-constructor-name make-mutator-shape)
    (def-struct struct-type-property-shape ([has-guard? boolean?])
      #:extra-constructor-name make-struct-type-property-shape)
    (def-struct property-predicate-shape ()
      #:extra-constructor-name make-property-predicate-shape)
    (def-struct property-accessor-shape ()
      #:extra-constructor-name make-property-accessor-shape)
    (def-struct struct-other-shape ()
      #:extra-constructor-name make-struct-other-shape))
  |#
  )
