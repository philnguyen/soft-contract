#lang typed/racket/base

(provide prims-04-03@)

(require racket/match
         racket/contract
         racket/bool
         racket/string
         racket/math
         racket/list
         racket/stream
         racket/dict
         racket/function
         racket/set
         racket/flonum
         racket/fixnum
         racket/generator
         racket/random
         racket/format
         racket/splicing
         typed/racket/unit
         syntax/parse/define
         set-extras
         "../utils/debug.rkt"
         (except-in "../ast/signatures.rkt" normalize-arity arity-includes?)
         "../runtime/signatures.rkt"
         "../proof-relation/signatures.rkt"
         "../signatures.rkt"
         "signatures.rkt"
         "def-prim.rkt"
         (for-syntax racket/base
                     racket/syntax
                     syntax/parse))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;; 4.3 Strings
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define-unit prims-04-03@
  (import proof-system^ prim-runtime^ local-prover^ widening^ for-gc^ val^ pc^ sto^)
  (export)

  ;; 4.3.1 Constructors, Selectors, Mutators
  (def-pred string?)
  (def-prim make-string ; FIXME all uses
    (exact-nonnegative-integer? char? . -> . (and/c string? (not/c immutable?))))
  (def-prim/custom (string ⟪ℋ⟫ ℓ Σ $ Γ Ws) ; FIXME uses, domain check
    (define σ (-Σ-σ Σ))
    (define sₐ (apply ?t@ 'string (map -W¹-t Ws)))
    {set (-ΓA Γ (-W (list (-● {set 'string? (-not/c 'immutable?)})) sₐ))})
  (def-prim string->immutable-string
    (string? . -> . (and/c string? immutable?)))
  (def-prim string-length
    (string? . -> . exact-nonnegative-integer?))
  (def-prim string-ref (string? exact-nonnegative-integer? . -> . char?))
  (def-prim string-set!
    ((and/c string? (not/c immutable?)) exact-nonnegative-integer? char? . -> . void?))
  (def-prim substring ; FIXME uses
    (string? exact-nonnegative-integer? exact-nonnegative-integer? . -> . string?))
  (def-prim string-copy
    (string . -> . string?))
  (def-prim/todo string-copy! ; FIXME uses
    ((and/c string? (not/c immutable?)) exact-nonnegative-integer? string? . -> . void?))
  (def-prim/todo string-fill! ; FIXME uses
    ((and/c string? (not/c immutable?)) char? . -> . void?))
  (def-prim string-append (() #:rest (listof string?) . ->* . string?)
    #:refinements
    (() #:rest (listof path-string?) . ->* . path-string?))
  (def-prim/custom (string->list ⟪ℋ⟫ ℓ Σ $ Γ Ws)
    #:domain ([W string?])
    (define σ (-Σ-σ Σ))
    (match-define (-W¹ V s) W)
    (define sₐ (?t@ 'string->list s))
    (match V
      [(-b "") {set (-ΓA Γ (-W (list -null) sₐ))}]
      [_
       (define αₕ (-α->⟪α⟫ (-α.fld -𝒾-cons ℓ ⟪ℋ⟫ 0)))
       (define αₜ (-α->⟪α⟫ (-α.fld -𝒾-cons ℓ ⟪ℋ⟫ 1)))
       (define Vₜ (-Cons αₕ αₜ))
       (σ⊕V! Σ αₕ (-● {set 'char?}))
       (σ⊕V! Σ αₜ Vₜ)
       (σ⊕V! Σ αₜ -null)
       (define Ans {set (-ΓA Γ (-W (list Vₜ) sₐ))})
       (match V
         [(-b (? string? s)) #:when (> (string-length s) 0) Ans]
         [_ (set-add Ans (-ΓA Γ (-W (list -null) sₐ)))])]))
  (def-prim/custom (list->string ⟪ℋ⟫ ℓ Σ $ Γ Ws)
    #:domain ([W (listof char?)])
    (define σ (-Σ-σ Σ))
    (match-define (-W¹ V s) W)
    (define sₐ (?t@ 'list->string s))
    (define ps
      (cond [(list-of-non-null-chars? σ V) ; FIXME needs to check for non-empty-ness too
             {set 'path-string? (-not/c 'immutable?)}]
            [else
             {set 'string? (-not/c 'immutable?)}]))
    {set (-ΓA Γ (-W (list (-● ps)) sₐ))})
  (def-prim/todo build-string
    (exact-nonnegative-integer? (exact-nonnegative-integer? . -> . char?) . -> . string?))

  ;; 4.3.2 String Comparisons. FIXME varargs
  (def-preds (string=? string<? string<=? string>? string>=?
                       string-ci=? string-ci<? string-ci<=? string-ci>? string-ci>=?)
    (string? string?))

  ;; 4.3.3 String Conversions
  (def-prims (string-upcase string-downcase string-titlecase string-foldcase
                            string-normalize-nfd string-normalize-nfkd
                            string-normalize-nfc string-normalize-nfkc)
    (string? . -> . string?))

  ;; 4.3.4 Locale-specific string operations 
  ; FIXME varargs
  (def-prims (string-locale=? string-locale<? string-locale>?
                              string-locale-ci=? string-locale-ci<? string-locale-ci>?)
    (string? string? . -> . string?))
  (def-prims (string-locale-upcase string-locale-downcase)
    (string? . -> . string?))

  ;; 4.3.5 Additional String Functions
  #;[string-append* #;FIXME]
  #;[string-join ; FIXME uses, listof
     ((listof string?) . -> . string?)]
  (def-prim string-normalize-spaces ; FIXME uses
    (string? . -> . string?))
  (def-prim string-replace ; FIXME uses
    (string? (or/c string? regexp?) string? . -> . string?))
  #;[string-split ; FIXME uses, listof
     (string? . -> . (listof string?))]
  (def-prim string-trim ; FIXME uses
    (string? . -> . string?))
  (def-pred non-empty-string?)
  [def-preds (string-contains? string-prefix? string-suffix?)
    (string? string?)]

  ;; 4.3.6 Converting Values to Strings.
  (def-prims (~a ~v ~s ~e ~.a ~.v ~.s) (any/c . -> . string?)) ; FIXME uses
  (def-prim ~r (rational? . -> . string?)) ; FIXME uses


  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
  ;;;;; HELPERS
  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (: list-of-non-null-chars? : -σ -V → Boolean)
  ;; Check if a value is definitely a list of non-null characters
  (define (list-of-non-null-chars? σ V)
    (define-set seen : ⟪α⟫ #:eq? #t #:as-mutable-hash? #t)
    (with-debugging/off ((ans) (let go : Boolean ([V : -V V])
                                    (match V
                                      [(-b (list)) #t]
                                      [(-Cons αₕ αₜ)
                                       (and (for/and : Boolean ([Vₕ (σ@ σ αₕ)])
                                              (equal? '✗ (p∋Vs σ 'equal? (-b #\null) Vₕ)))
                                            (or
                                             (seen-has? αₜ)
                                             (begin
                                               (seen-add! αₜ)
                                               (for/and : Boolean ([Vₜ (σ@ σ αₜ)])
                                                 (go Vₜ)))))]
                                      [_ #f])))
      (printf "list-of-non-null-char? ~a -> ~a~n"
              (show-V V) ans)
      (define αs (V->⟪α⟫s V))
      (for ([(α Vs) (in-hash σ)] #:when (∋ αs α))
        (printf "  - ~a ↦ ~a~n" (show-⟪α⟫ (cast α ⟪α⟫)) (set-map Vs show-V)))
      (printf "~n")))
  )
