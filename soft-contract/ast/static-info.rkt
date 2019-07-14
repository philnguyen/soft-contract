#lang typed/racket/base

(provide static-info@)

(require racket/match
         racket/set
         (only-in racket/string string-join)
         typed/racket/unit
         set-extras
         "signatures.rkt")

(define-unit static-info@
  (import ast-pretty-print^)
  (export static-info^)

  (define primitive-struct-info : (Immutable-HashTable -𝒾 -struct-info)
    (hash -𝒾-cons (Vector->struct-info (vector-immutable (cons 'car #f) (cons 'cdr #f)))
          -𝒾-mcons (Vector->struct-info (vector-immutable (cons 'mcar #t) (cons 'mcdr #t)))
          -𝒾-box (Vector->struct-info (vector-immutable (cons 'unbox #t)))
          -𝒾-thread-cell (Vector->struct-info (vector-immutable (cons 'thread-cell-ref #t)))))

  (define (new-static-info)
    (-static-info (make-hash (hash->list primitive-struct-info))
                  (make-hash (list (cons -𝒾-cons {set -car -cdr})
                                   (cons -𝒾-mcons {set -mcar -mcdr})
                                   (cons -𝒾-box {set -unbox})
                                   (cons -𝒾-thread-cell {set -thread-cell-ref})))
                  (make-hash (list (cons -𝒾-mcons {set -set-mcar! -set-mcdr!})
                                   (cons -𝒾-box (set -set-box!))
                                   (cons -𝒾-thread-cell {set -set-thread-cell!})))
                  (make-hash)
                  (make-hash)
                  (make-hash)
                  (make-hash)
                  (make-hash)
                  (make-hash)
                  (make-hash)
                  (make-hash)))

  (define current-static-info : (Parameterof -static-info) (make-parameter (new-static-info)))

  (define-syntax-rule (with-initialized-static-info e ...)
    (parameterize ([current-static-info (new-static-info)])
      e ...))


  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
  ;;;;; Querying struct information
  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (: get-struct-info : -𝒾 → -struct-info)
  (define (get-struct-info 𝒾)
    (define structs (-static-info-structs (current-static-info)))
    (hash-ref
     structs 𝒾
     (λ ()
       (error 'get-struct-info "Nothing for ~a among ~a"
              (show-𝒾 𝒾)
              (string-join (map show-𝒾 (hash-keys structs))
                           ", "
                           #:before-first "["
                           #:after-last "]")))))

  ;; Return number of fields that this struct directly declares
  (define (count-direct-struct-fields [𝒾 : -𝒾]) : Index (vector-length (get-struct-info 𝒾)))
  (define (struct-mutable? [𝒾 : -𝒾] [i : Natural]) (cdr (vector-ref (get-struct-info 𝒾) (- i (struct-offset 𝒾)))))
  (define (struct-all-immutable? [𝒾 : -𝒾])
    (not (for/or : Boolean ([fld-info (in-vector (get-struct-info 𝒾))])
           (cdr fld-info))))
  (define (struct-direct-accessor-names [𝒾 : -𝒾])
    (define pre (-𝒾-name 𝒾))
    (for/list : (Listof Symbol) ([fld (in-vector (get-struct-info 𝒾))])
      (car fld)))
  (define (struct-accessor-name [𝒾 : -𝒾] [i : Integer]) : Symbol
    (define o (struct-offset 𝒾))
    (if (>= i o)
        (car (vector-ref (get-struct-info 𝒾) (- i o)))
        (let ([𝒾* (hash-ref (-static-info-parentstruct (current-static-info)) 𝒾)])
          (struct-accessor-name 𝒾* (- i o)))))
  (define (add-struct-info! [𝒾 : -𝒾] [direct-fields : (Listof Symbol)] [mutables : (Setof Natural)])
    (define v
      (vector->immutable-vector
       (for/vector : (Vectorof (Pairof Symbol Boolean)) #:length (length direct-fields)
                   ([(fld i) (in-indexed direct-fields)])
                   (cons fld (∋ mutables i)))))
    (define m (-static-info-structs (current-static-info)))
    (cond
      [(hash-ref m 𝒾 #f) =>
        (λ ([v₀ : -struct-info])
          (cond [(equal? v₀ v) (void)]
                [else (error 'add-struct-info!
                             "inconsistent struct information for ~a:~n - ~a~n - ~a"
                             (-𝒾-name 𝒾)
                             v₀
                             v)]))]
      [else
       (hash-set! m 𝒾 (Vector->struct-info v))]))

  (: get-public-accs : -𝒾 → (℘ -st-ac))
  (define (get-public-accs 𝒾)
    (hash-ref (-static-info-public-accs (current-static-info))
              𝒾
              mk-∅))

  (: add-public-acc! : -𝒾 -st-ac → Void)
  (define (add-public-acc! 𝒾 ac)
    (hash-update! (-static-info-public-accs (current-static-info))
                  𝒾
                  (λ ([acs : (℘ -st-ac)])
                    (set-add acs ac))
                  mk-∅))

  (: get-public-muts : -𝒾 → (℘ -st-mut))
  (define (get-public-muts 𝒾)
    (hash-ref (-static-info-public-muts (current-static-info))
              𝒾
              mk-∅))

  (: add-public-mut! : -𝒾 -st-mut → Void)
  (define (add-public-mut! 𝒾 mut)
    (hash-update! (-static-info-public-muts (current-static-info))
                  𝒾
                  (λ ([muts : (℘ -st-mut)])
                    (set-add muts mut))
                  mk-∅))


  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
  ;;;;; Export alias
  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (: set-export-alias! : -𝒾 -𝒾 → Void)
  (define (set-export-alias! 𝒾ᵢₙ 𝒾ₒᵤₜ)
    (define export-aliases (-static-info-export-aliases (current-static-info)))
    (cond [(hash-ref export-aliases 𝒾ᵢₙ #f) =>
                                            (λ ([𝒾₀ : -𝒾])
                                              (unless (equal? 𝒾₀ 𝒾ₒᵤₜ)
                                                (error 'set-export-aliases! "~a already maps to ~a, set to ~a"
                                                       (show-𝒾 𝒾ᵢₙ) (show-𝒾 𝒾₀) (show-𝒾 𝒾ₒᵤₜ))))]
          [else
           (hash-set! export-aliases 𝒾ᵢₙ 𝒾ₒᵤₜ)]))

  (: get-export-alias (∀ (X) ([-𝒾] [(→ X)] . ->* . (U X -𝒾))))
  (define (get-export-alias 𝒾 [on-failure (λ () (error 'get-export-alias "nothing for ~a" (show-𝒾 𝒾)))])
    (hash-ref (-static-info-export-aliases (current-static-info)) 𝒾 on-failure))


  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
  ;;;;; Module initialization dependency
  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (: module-before? : -l -l → Boolean)
  (define (module-before? l1 l2)
    (∋ (hash-ref (-static-info-dependencies (current-static-info)) l2 mk-∅) l1))

  (: set-module-before! : -l -l → Void)
  (define (set-module-before! l1 l2)
    (define deps (-static-info-dependencies (current-static-info)))
    (hash-update! deps l2
                  (λ ([ls : (℘ -l)])
                    (∪ ls (set-add (hash-ref deps l1 mk-∅) l1)))
                  mk-∅))


  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
  ;;;;; Alternate aliases
  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (: set-alternate-alias! : -𝒾 -𝒾 Boolean → Void)
  (define (set-alternate-alias! 𝒾ᵢₙ 𝒾ₒᵤₜ wrap?)
    (define alternate-aliases (-static-info-alternate-aliases (current-static-info)))
    (cond [(hash-ref alternate-aliases 𝒾ᵢₙ #f) =>
                                               (match-lambda
                                                 [(cons 𝒾₀ wrap?₀)
                                                  (unless (and (equal? 𝒾₀ 𝒾ₒᵤₜ) (equal? wrap? wrap?₀))
                                                    (error 'set-alternate-alias! "~a already maps to ~a, set to ~a"
                                                           (show-𝒾 𝒾ᵢₙ) (show-𝒾 𝒾₀) (show-𝒾 𝒾ₒᵤₜ)))])]
          [else
           (hash-set! alternate-aliases 𝒾ᵢₙ (cons 𝒾ₒᵤₜ wrap?))]))

  (: get-alternate-alias (∀ (X) ([-𝒾] [(→ X)] . ->* . (U X (Pairof -𝒾 Boolean)))))
  (define (get-alternate-alias 𝒾 [on-failure (λ () (error 'get-alternate-alias "nothing for ~a" (show-𝒾 𝒾)))])
    (hash-ref (-static-info-alternate-aliases (current-static-info)) 𝒾 on-failure))

  (: set-alternate-alias-id! : -l Symbol → Void)
  (define (set-alternate-alias-id! l id)
    (define alternate-alias-ids (-static-info-alternate-alias-ids (current-static-info)))
    (cond [(hash-ref alternate-alias-ids l #f) =>
                                               (λ ([id₀ : Symbol])
                                                 (unless (equal? id₀ id)
                                                   (error 'set-alternate-alias-id! "~a already maps to ~a, set to ~a" l id₀ id)))]
          [else (hash-set! alternate-alias-ids l id)]))

  (: get-alternate-alias-id (∀ (X) ([-l] [(→ X)] . ->* . (U X Symbol))))
  (define (get-alternate-alias-id l [on-failure (λ () (error 'get-alternate-flag-id "nothing for ~a" l))])
    (hash-ref (-static-info-alternate-alias-ids (current-static-info)) l on-failure))


  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
  ;;;;; Assignables
  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (: assignable? : (U Symbol -𝒾) → Boolean)
  (define (assignable? x)
    (hash-has-key? (-static-info-assignables (current-static-info)) x))

  (: set-assignable! : (U Symbol -𝒾) → Void)
  (define (set-assignable! x)
    (hash-set! (-static-info-assignables (current-static-info)) x #t))


  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
  ;;;;; Superstructs
  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (: in-struct-tags : → (Sequenceof -𝒾))
  (define (in-struct-tags)
    (in-hash-keys (-static-info-structs (current-static-info))))

  (: set-parent-struct! : -𝒾 -𝒾 → Void)
  (define (set-parent-struct! 𝒾-sub 𝒾-sup)
    (define parentstruct (-static-info-parentstruct (current-static-info)))
    (cond [(hash-ref parentstruct 𝒾-sub #f)
           =>
           (λ ([𝒾₀ : -𝒾])
             (unless (equal? 𝒾₀ 𝒾-sup)
               (error 'add-parent-struct! "already have ~a as ~a's parent, adding ~a"
                      (-𝒾-name 𝒾₀) (-𝒾-name 𝒾-sub) (-𝒾-name 𝒾-sup))))]
          [else
           (hash-set! parentstruct 𝒾-sub 𝒾-sup)]))

  (: substruct? : -𝒾 -𝒾 → Boolean)
  (define (substruct? 𝒾-sub 𝒾-sup)
    (define parentstruct (-static-info-parentstruct (current-static-info)))
    (let loop ([𝒾 : -𝒾 𝒾-sub])
      (cond [(equal? 𝒾 𝒾-sup) #t]
            [(hash-ref parentstruct 𝒾 #f) => loop]
            [else #f])))

  (: struct-offset : -𝒾 → Index)
  ;; Return the total number of fields from super-structs
  (define (struct-offset 𝒾)
    ;; NOTE: maybe unsafe to memoize this function because it depends on parameter
    (define parentstruct (-static-info-parentstruct (current-static-info)))
    (let loop ([𝒾 : -𝒾 𝒾] [n : Index 0])
      (match (hash-ref parentstruct 𝒾 #f)
        [(? values 𝒾*) (loop 𝒾* (assert (+ n (count-direct-struct-fields 𝒾*)) index?))]
        [#f n])))

  (: count-struct-fields : -𝒾 → Index)
  ;; Return the total number of fields in struct, including its super-structs
  (define (count-struct-fields 𝒾)
    (assert (+ (struct-offset 𝒾) (count-direct-struct-fields 𝒾)) index?))

  (: add-transparent-module! : -l → Void)
  (define (add-transparent-module! l)
    (hash-set! (-static-info-transparent-modules (current-static-info)) l #t))

  (: transparent-module? : -l → Boolean)
  (define (transparent-module? l)
    (hash-has-key? (-static-info-transparent-modules (current-static-info)) l))

  (: prim-struct? : -𝒾 → Boolean)
  (define (prim-struct? 𝒾) (hash-has-key? primitive-struct-info 𝒾))

  (: set-struct-alias! : -𝒾 -𝒾 → Void)
  (define (set-struct-alias! 𝒾-ref 𝒾-def)
    (define m (-static-info-struct-alias (current-static-info)))
    (match (hash-ref m 𝒾-ref #f)
      [#f (hash-set! m 𝒾-ref 𝒾-def)]
      [(== 𝒾-def) (void)]
      [(? values 𝒾*) (error 'set-struct-alias! "~a ↦ ~a, attempt to set to ~a"
                            (show-𝒾 𝒾-ref) (show-𝒾 𝒾*) (show-𝒾 𝒾-def))]))

  (: resolve-struct-alias : -𝒾 → -𝒾)
  (define (resolve-struct-alias 𝒾)
    (hash-ref (-static-info-struct-alias (current-static-info)) 𝒾 (λ () 𝒾)))
  )
