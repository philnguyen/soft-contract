#lang typed/racket/base

;; This module provides static information about the program available from parsing

(provide with-initialized-static-info
         get-struct-arity
         struct-all-immutable?
         struct-mutable?
         add-struct-info!
         add-top-level!
         top-levels
         get-public-accs
         get-public-muts
         add-public-acc!
         add-public-mut!
         current-static-info ; just for debugging
         get-export-alias
         set-export-alias!
         )

(require racket/match
         racket/set
         "../utils/set.rkt"
         "definition.rkt"
         "shorthands.rkt")

(define-new-subtype -struct-info (Vector->struct-info (Vectorof Boolean)))
(struct -static-info ([structs : (HashTable -𝒾 -struct-info)]
                      [public-accs : (HashTable -𝒾 (℘ -st-ac))]
                      [public-muts : (HashTable -𝒾 (℘ -st-mut))]
                      [top-level-defs : (HashTable -𝒾 #t)]
                      [export-aliases : (HashTable -𝒾 -𝒾)])
  #:transparent)

(define (new-static-info)
  (define cons-info (Vector->struct-info (vector-immutable #f #f)))
  (define mcons-info (Vector->struct-info (vector-immutable #t #t)))
  (define box-info (Vector->struct-info (vector-immutable #t)))
  (-static-info (make-hash (list (cons -𝒾-cons cons-info)
                                 (cons -𝒾-mcons mcons-info)
                                 (cons -𝒾-box  box-info)))
                (make-hash (list (cons -𝒾-cons {set -car -cdr})
                                 (cons -𝒾-mcons {set -mcar -mcdr})
                                 (cons -𝒾-box (set -unbox))))
                (make-hash (list (cons -𝒾-mcons {set -set-mcar! -set-mcdr!})
                                 (cons -𝒾-box (set -set-box!))))
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
  (hash-ref structs 𝒾 (λ () (error 'get-struct-info "Nothing for ~a" (-𝒾-name 𝒾)))))

(define (get-struct-arity [𝒾 : -𝒾]) : Index (vector-length (get-struct-info 𝒾)))
(define (struct-mutable? [𝒾 : -𝒾] [i : Index]) (vector-ref (get-struct-info 𝒾) i))
(define (struct-all-immutable? [𝒾 : -𝒾])
  (not (for/or : Boolean ([mut? (in-vector (get-struct-info 𝒾))])
         mut?)))
(define (add-struct-info! [𝒾 : -𝒾] [arity : Index] [mutables : (Setof Index)])
  (define v
    (for/vector : (Vectorof Boolean) #:length arity ([i arity])
      (∋ mutables i)))
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
            →∅))

(: add-public-acc! : -𝒾 -st-ac → Void)
(define (add-public-acc! 𝒾 ac)
  (hash-update! (-static-info-public-accs (current-static-info))
                𝒾
                (λ ([acs : (℘ -st-ac)])
                  (set-add acs ac))
                →∅))

(: get-public-muts : -𝒾 → (℘ -st-mut))
(define (get-public-muts 𝒾)
  (hash-ref (-static-info-public-muts (current-static-info))
            𝒾
            →∅))

(: add-public-mut! : -𝒾 -st-mut → Void)
(define (add-public-mut! 𝒾 mut)
  (hash-update! (-static-info-public-muts (current-static-info))
                𝒾
                (λ ([muts : (℘ -st-mut)])
                  (set-add muts mut))
                →∅))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;; Querying top-level definitions
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define (add-top-level! [𝒾 : -𝒾])
  (hash-set! (-static-info-top-level-defs (current-static-info)) 𝒾 #t))
(define (top-levels) : (Listof -𝒾)
  (hash-keys (-static-info-top-level-defs (current-static-info))))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;; Export alias
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(: set-export-alias! : -𝒾 -𝒾 → Void)
(define (set-export-alias! 𝒾ᵢₙ 𝒾ₒᵤₜ)
  (define export-aliases (-static-info-export-aliases (current-static-info)))
  (cond [(hash-ref export-aliases 𝒾ᵢₙ #f) =>
         (λ ([𝒾₀ : -𝒾])
           (error 'set-export-aliases! "~a already maps to ~a, set to ~a"
                  (show-𝒾 𝒾ᵢₙ) (show-𝒾 𝒾₀) (show-𝒾 𝒾ₒᵤₜ)))]
        [else
         (hash-set! export-aliases 𝒾ᵢₙ 𝒾ₒᵤₜ)]))

(: get-export-alias ([-𝒾] [(→ -𝒾)] . ->* . -𝒾))
(define (get-export-alias 𝒾 [on-failure (λ () (error 'get-export-alias "nothing for ~a" (show-𝒾 𝒾)))])
  (hash-ref (-static-info-export-aliases (current-static-info)) 𝒾 on-failure))
