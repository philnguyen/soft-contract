#lang typed/racket/base

(provide (all-defined-out))

(require racket/match "../ast/definition.rkt" "../utils/def.rkt" "val.rkt")
(require/typed "../primitives/declarations.rkt"
 [(prims prims:prims) (Listof Any)])

;; Representation of arity in the meta-language to make it easier to manipulate
;; in proof rules.
;; In the object language, it's just Racket's numbers and lists.
(define-data -Arity
  (subset: -Simple-Arity
    Integer
    (struct -Arity-At-Least [val : Integer]))
  (Listof -Simple-Arity))

(: -arity-includes? : -Arity -Arity → Boolean)
;; Check if arity `ar₁` subsumes `ar₂`
(define (-arity-includes? ar₁ ar₂)

  (define (-arity-supports-number? [ar : -Arity] [n : Integer]) : Boolean
    (match ar
      [(? exact-integer? m) (= m n)]
      [(-Arity-At-Least m) (<= m n)]
      [(? list? ars) (for/or ([ari ars]) (-arity-supports-number? ari n))]))

  (define (-arity-supports-at-least? [ar : -Arity] [n : Integer]) : Boolean
    (match ar
      [(? exact-integer?) #f]
      [(-Arity-At-Least m) (<= m n)]
      [(? list? ars)
       (define min-at-least
         (for/fold ([min-at-least : (Option Integer) #f])
                   ([ari ars])
           (match ari
             [(? exact-integer?) min-at-least]
             [(-Arity-At-Least m)
              (cond [min-at-least (min min-at-least m)]
                    [else m])])))
       (and min-at-least
            (for/and ([i (in-range n min-at-least)])
              (-arity-supports-number? ar i)))]))
  
  (match ar₂
    [(? exact-integer? n) (-arity-supports-number? ar₁ n)]
    [(-Arity-At-Least n) (-arity-supports-at-least? ar₁ n)]
    [(? list? ars₂) (for/and ([ari ars₂]) (-arity-includes? ar₁ ari))]))

(: -procedure-arity : -V → (Option -Arity))
;; Return given value's arity
(define -procedure-arity
  (let ()
    
    (define (-formals-arity [xs : -formals]) : -Arity
      (cond
        [(-varargs? xs) (-Arity-At-Least (length (-varargs-init xs)))]
        [else (length xs)]))

    (define (-guard-arity [guard : -=>i]) : -Arity
      (match-define (-=>i xs _ _ rst _ _ _) guard)
      (define n (length xs))
      (cond [rst (-Arity-At-Least n)]
            [else n]))

    (define arity-table
      (for/fold ([m : (HashTable Symbol -Arity) (hasheq)]) ([dec prims:prims])
        (match dec
          [`(#:pred ,(? symbol? s)) (hash-set m s 1)]
          [`(#:pred ,(? symbol? s) (,xs ...)) (hash-set m s (length xs))]
          [`(#:batch (,ss ...) (,xs ... . -> . ,_) ,_ ...)
           (define n (length xs))
           (for/fold ([m : (HashTable Symbol -Arity) m]) ([s ss])
             (hash-set m (assert s symbol?) n))]
          [`(#:batch (,ss ...) (,xs #:rest ,_ . ->* . ,_) ,_ ...)
           (define n (-Arity-At-Least (length (assert xs list?))))
           (for/fold ([m : (HashTable Symbol -Arity) m]) ([s ss])
             (hash-set m (assert s symbol?) n))]
          [`(,(? symbol? s) (,xs ... . -> . ,_) ,_ ...)
           (hash-set m s (length xs))]
          [`(,(? symbol? s) (,xs #:rest ,_ . ->* . ,_) ,_ ...)
           (hash-set m s (-Arity-At-Least (length (assert xs list?))))]
          [_ m])))

    (match-lambda
      [(or (-Clo xs _ _ _) (-Clo* xs _ _)) (-formals-arity (assert xs))]
      [(or (-And/C #t _ _) (-Or/C #t _ _) (? -Not/C?)) 1]
      [(-Ar guard _ _) (-guard-arity guard)]
      [(? -st-p?) 1]
      [(-st-mk (-struct-info _ n _)) n]
      [(? -st-ac?) 1]
      [(? -st-mut?) 2]
      [(? symbol? s) (hash-ref arity-table s)]
      [(-●) #f]
      [V (error '-procedure-arity "called on a non-procedure ~a" (show-V V))])))

(module+ test
  (require typed/rackunit)
  (check-true (-arity-includes? 1 1) "1-1")
  (check-true (-arity-includes? (list 1) 1) "(1)-1")
  (check-true (-arity-includes? 1 (list 1)) "1-(1)")
  (check-false (-arity-includes? 1 (-Arity-At-Least 1)) "1-≥1")
  (check-true (-arity-includes? (-Arity-At-Least 1) 1) "≥1-1")
  (check-true (-arity-includes? (-Arity-At-Least 1) (list 1 (-Arity-At-Least 2))) "≥1-1")
  (check-true (-arity-includes? (list 1 (-Arity-At-Least 2)) (-Arity-At-Least 1))
              "(1,≥2)-≥1")
  (check-true (-arity-includes? (-Arity-At-Least 1) (list 1 (-Arity-At-Least 3)))
              "≥1-(1,≥3)")
  (check-false (-arity-includes? (list 1 (-Arity-At-Least 3)) (-Arity-At-Least 1))
               "(1,≥3)-≥1")
  (check-true (-arity-includes? (list 0 1 2 (-Arity-At-Least 3))
                                (list (-Arity-At-Least 0)))
              "(0,1,2,≥3)-≥0")
  (check-true (-arity-includes? (list (-Arity-At-Least 0))
                                (list 0 1 2 (-Arity-At-Least 3)))
              "(≥0)-(0,1,2,≥3)")
  (check-false (-arity-includes? (list 0 2 (-Arity-At-Least 3))
                                 (list (-Arity-At-Least 0)))
               "(0,2,≥3)-(≥0)")
  (check-true (-arity-includes? (list (-Arity-At-Least 0))
                                (list 0 2 (-Arity-At-Least 3)))
              "(≥0)-(0,2,≥3)"))
