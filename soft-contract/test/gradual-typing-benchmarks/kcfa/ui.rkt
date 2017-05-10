#lang racket/base

;; User Interface to `ai.rkt`

(require
  require-typed-check
  racket/set
  "structs.rkt"
  "benv.rkt"
  "denotable.rkt"
  "time.rkt"
  (only-in racket/string string-join)
)

(require "ai.rkt")
;(require/typed/check "ai.rkt"
;  (atom-eval (-> BEnv Store (-> Exp Denotable)))
;  (next (-> State (Setof State)))
;  (explore (-> (Setof State) (Listof State) (Setof State)))
;)
;; ---

(provide
  summarize
  empty-mono-store
  monovariant-value
  monovariant-store
  analyze
  format-mono-store
)

;; =============================================================================

;; -- ui.rkt
;(define-type MonoStore (HashTable Var (Setof Exp)))

;(: summarize (-> (Setof State) Store))
(define (summarize states)
  (for/fold ([store empty-store])
    ([state (in-set states)])
    (store-join (State-store state) store)))

;(: empty-mono-store MonoStore)
(define empty-mono-store (make-immutable-hasheq '()))

;(: monovariant-value (-> Value Lam))
(define (monovariant-value v)
  (Closure-lam v))

;(: monovariant-store (-> Store MonoStore))
(define (monovariant-store store)
  ;(: update-lam (-> (Setof Value) (-> (Setof Exp) (Setof Exp))))
  (define ((update-lam vs) b-vs)
    ;(: v-vs (Setof Lam))
    (define v-vs (list->set (set-map vs monovariant-value)))
    (set-union b-vs v-vs))
  ;(: default-lam (-> (Setof Exp)))
  (define (default-lam) (set))
  (for/fold ([mono-store empty-mono-store])
    ([(b vs) (in-hash store)])
    (hash-update mono-store
                 (Binding-var b)
                 (update-lam vs)
                 default-lam)))

;(: analyze (-> Exp MonoStore))
(define (analyze exp)
  (define init-state (State exp empty-benv empty-store time-zero))
  (define states (explore (set) (list init-state)))
  (define summary (summarize states))
  (define mono-store (monovariant-store summary))
  mono-store)

;(: format-mono-store (-> MonoStore String))
(define (format-mono-store ms)
  ;(: res (Listof String))
  (define res
    (for/list ([(i vs) (in-hash ms)])
      (format "~a:\n~a"
              i
              (string-join
                (for/list ([v (in-set vs)])
                  (format "\t~S" v))
                "\n"))))
  (string-join res "\n"))

