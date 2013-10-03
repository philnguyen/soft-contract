#lang racket
(require redex)
(provide MT \\ ∪ env@ env+ env-has? dom ≠)

(define-language MT
  [any* (any ...)]
  [env ([any ↦ any] ...)])


;; set operation\s

(define-metafunction MT
  \\ : any* any* -> any*
  [(\\ any {}) any]
  [(\\ (any_1 ... any any_2 ...) (any any_r ...)) (\\ (any_1 ... any_2 ...) (any_r ...))]
  [(\\ any_* (any any_r ...)) (\\ any_* (any_r ...))])

(define-metafunction MT
  ∪ : any* ... -> any*
  [(∪ {any ...} ...) ,(set->list (list->set (apply append (term ((any ...) ...)))))])


;; generic environment operations

(define-metafunction MT
  env@ : env any -> any
  [(env@ (any_1 ... [any_k ↦ any_v] any_2 ...) any_k) any_v])

(define-metafunction MT
  env+ : env any any -> env
  [(env+ (any_1 ... [any_k ↦ any_v] any_2 ...) any_k any_u) (any_1 ... [any_k ↦ any_u] any_2 ...)]
  [(env+ (any ...) any_k any_v) ([any_k ↦ any_v] any ...)])

(define-metafunction MT
  env-has? : env any -> #t or #f
  [(env-has? (any_1 ... [any ↦ any_v] any_i ...) any) #t]
  [(env-has? any_env any) #f])

(define-metafunction MT
  dom : env -> (any ...)
  [(dom ([any_k ↦ any_v] ...)) (any_k ...)])

(define-metafunction MT
  ≠ : any any -> #t or #f
  [(≠ any any) #f]
  [(≠ any ...) #t])