#lang racket

;; Denotable values and stores to hold them.
;; A denotable is a set of values
;; (A value is a closure)

(require
  #;require-typed-check
  "structs.rkt"
  "benv.rkt"
  "time.rkt"
)

;; -----------------------------------------------------------------------------

(provide
 Denotable/c
 Store/c
 (contract-out
  [d-bot Denotable/c]
  [d-join (Denotable/c Denotable/c . -> . Denotable/c)]
  [empty-store Store/c]
  [store-lookup (Store/c Addr/c . -> . Denotable/c)]
  [store-update (Store/c Addr/c Denotable/c . -> . Store/c)] ; fixed once implement hash-update
  [store-update* (Store/c (listof Addr/c) (listof Denotable/c) . -> . Store/c)] ; fixed once implement hash-update
  [store-join (Store/c Store/c . -> . Store/c)] ; fixed once implement hash-update
  [struct State ([call exp/c] [benv BEnv/c] [store Store/c] [time Time/c])])
)

;; =============================================================================

;; -- private
;(define-type Denotable (Setof Value))
;(define-type Store (HashTable Addr Denotable))

;; -- structs

(struct State
 (call ;: Exp]
  benv ;: BEnv]
  store ;: Store]
  time ;: Time]))
))
;; -- public

;(: d-bot Denotable)
(define d-bot (set))

;(: d-join (-> Denotable Denotable Denotable))
(define d-join set-union)

;(: empty-store Store)
(define empty-store (make-immutable-hasheq '()))

;(: store-lookup (-> Store Addr Denotable))
(define (store-lookup s a)
  (hash-ref s a (lambda () d-bot)))

;(: store-update (-> Store Addr Denotable Store))
(define (store-update store addr value)
  ;(: update-lam (-> Denotable Denotable))
  (define (update-lam d) (d-join d value))
  (hash-update store addr update-lam (lambda () d-bot)))

;(: store-update* (-> Store (Listof Addr) (Listof Denotable) Store))
(define (store-update* s as vs)
  (for/fold ([store s])
    ([a (in-list as)]
     [v (in-list vs)])
    (store-update store a v)))

;(: store-join (-> Store Store Store))
(define (store-join s1 s2)
  (for*/fold ([new-store s1])
             ;; FIXME this should be fixed once the primitives DSL is generalized
             ([k (in-hash-keys s2)]
              [v (in-value (hash-ref s2 k))])
             #;([(k v) (in-hash s2)])
    
    (store-update new-store k v)))

(define Denotable/c set?) ; FIXME
(define Store/c (and/c immutable? (hash/c Addr/c Denotable/c)))
