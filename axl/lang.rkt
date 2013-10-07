#lang racket
(require redex)

(provide L \\ ∪ env@ env+ env-has? dom ≠)

(define-language L
  ; source program syntax
  [(p q) (m ... e)]
  [m (def x v)]
  [e v x (e e) (o e ...) (if e e e)]
  [v (λ (x) e) b ⊤]
  [b #t #f n empty INT PROC]
  [o o1 o2]
  [o1 o? ac add1]
  [o2 cons * + - =]
  [o? int? false? cons? empty? proc? tt]
  [ac car cdr]
  [n integer]
  [(x y z X Y Z) variable-not-otherwise-mentioned]
  [(x* y* z* f* l*) (x ...)]
  [n• n INT]
  [n+⊤ n• ⊤]
  [PROC• PROC (⇓ (λ (x) e) ρ)]

  [B #t #f]
  
  ; generic
  [any* (any ...)]
  [env ([any ↦ any] ...)])


;;;;; set operation\s

(define-metafunction L
  \\ : any* any* -> any*
  [(\\ any {}) any]
  [(\\ (any_1 ... any any_2 ...) (any any_r ...)) (\\ (any_1 ... any_2 ...) (any_r ...))]
  [(\\ any_* (any any_r ...)) (\\ any_* (any_r ...))])

(define-metafunction L
  ∪ : any* ... -> any*
  [(∪ {any ...} ...) ,(set->list (list->set (apply append (term ((any ...) ...)))))])


;;;;; generic environment operations

(define-metafunction L
  env@ : env any -> any
  [(env@ (any_1 ... [any_k ↦ any_v] any_2 ...) any_k) any_v])

(define-metafunction L
  env+ : env any any -> env
  [(env+ (any_1 ... [any_k ↦ any_v] any_2 ...) any_k any_u) (any_1 ... [any_k ↦ any_u] any_2 ...)]
  [(env+ (any ...) any_k any_v) ([any_k ↦ any_v] any ...)])

(define-metafunction L
  env-has? : env any -> #t or #f
  [(env-has? (any_1 ... [any ↦ any_v] any_i ...) any) #t]
  [(env-has? any_env any) #f])

(define-metafunction L
  dom : env -> (any ...)
  [(dom ([any_k ↦ any_v] ...)) (any_k ...)])

(define-metafunction L
  ≠ : any any -> #t or #f
  [(≠ any any) #f]
  [(≠ any ...) #t])