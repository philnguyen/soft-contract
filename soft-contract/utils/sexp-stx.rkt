#lang typed/racket/base

(provide Sexps mk-cond sexp-and sexp-or tt? ff?)

(require racket/match racket/list)

(define-type Sexps (Listof Sexp))

;; Check for syntax of `#t` and `#f`
(define (tt? [x : Sexp]) (equal? #t x))
(define (ff? [x : Sexp]) (equal? #f x))

;; Make syntax for conjunction and disjunction with slight simplifications
(define (sexp-and [es : Sexps]) : Sexp
  (match (filter-not tt? es)
    ['() #t]
    [(list _ ... (? ff?) _ ...) #f]
    [(list e) e]
    [es `(and ,@es)]))
(define (sexp-or [es : Sexps]) : Sexp
  (match (filter-not ff? es)
    ['() #f]
    [(list _ ... (? tt?) _ ...) #t]
    [(list e) e]
    [es `(or ,@es)]))

;; Convert contract (as sexp) to condition on given identifier
(define (mk-cond [x : Symbol] [c : Sexp]) : Sexp
  (let go : Sexp ([c : Sexp c])
    (match c
      ['any/c #t]
      ['none/c #f]
      ['integer? `(exact-integer? ,x)]
      [(? symbol? p) `(,p ,x)]
      [`(not/c ,(? symbol? p)) `(not (,p ,x))]
      [`(and/c ,ps ...) (sexp-and (map go (cast ps Sexps)))]
      [`(or/c ,ps ...) (sexp-or (map go (cast ps Sexps)))])))
