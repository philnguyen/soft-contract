#lang racket

;; Binding environment,
;; helper functions

(require
  "structs.rkt"
)

(provide
 Time/c
 Var/c
 Addr/c
 (contract-out
  [struct Closure ([lam Lam/c] [benv BEnv/c])]
  [struct Binding ([var Var/c] [time Time/c])]
  [empty-benv BEnv/c]
  [benv-lookup (BEnv/c Var/c . -> . Addr/c)]
  [benv-extend (BEnv/c Var/c Addr/c . -> . BEnv/c)]
  [benv-extend* (BEnv/c (listof Var/c) (listof Addr/c) . -> . BEnv/c)])
)

;; =============================================================================

;; -- private

;(define-type BEnv (HashTable Var Addr))
;(define-type Addr Binding)
;(define-type Time (Listof Label))

;; -- structs

(struct Closure
 (lam ;: Lam]
  benv ;: BEnv]))
))
(struct Binding
 (var ;: Var]
  time ;: Time]))
))
;; -- public

;(: empty-benv BEnv)
(define empty-benv (make-immutable-hasheq '()))

;(: benv-lookup (-> BEnv Var Addr))
(define benv-lookup hash-ref)

;(: benv-extend (-> BEnv Var Addr BEnv))
(define benv-extend hash-set)

;(: benv-extend* (-> BEnv (Listof Var) (Listof Addr) BEnv))
(define (benv-extend* benv vars addrs)
  (for/fold ([benv benv])
    ([v (in-list vars)]
     [a (in-list addrs)])
    (benv-extend benv v a)))

(define Label/c symbol?)
(define Time/c (listof Label/c))
(define Var/c symbol?)
(define Addr/c (struct/c Binding Var/c Time/c))
(define BEnv/c (and/c immutable? (hash/c Var/c Addr/c)))

