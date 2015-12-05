#lang typed/racket/base

(provide (all-defined-out))
(require
 racket/set racket/match racket/function
 "../utils/set.rkt" "../utils/def.rkt" "../utils/pretty.rkt" "definition.rkt")
(require/typed redex/reduction-semantics
  [variable-not-in ((Listof Symbol) Symbol → Symbol)])


(define -tt (-b #t))
(define -ff (-b #f))
(define -null (-b null))

(define -s-cons (-struct-info 'cons 2 ∅))
(define -cons (-st-mk -s-cons))
(define -car (-st-ac -s-cons 0))
(define -cdr (-st-ac -s-cons 1))
(define -cons? (-st-p -s-cons))

(define -zero (-b 0))
(define -one (-b 1))

(define -s-box  (-struct-info 'box  1 {set 0}))
(define -box? (-st-p -s-box))
(define -unbox (-st-ac -s-box 0))
(define -box (-st-mk -s-box))
(define -set-box! (-st-mut -s-box 0))

(: --> : (Listof -e) -e Integer → -e)
;; Make a non-dependent contract as a special case of dependent contract
(define (--> cs d pos)
  (define doms
    (for/list : (Listof (Pairof Symbol -e)) ([(c i) (in-indexed cs)])
      (define x (string->symbol (format "x•~a" (n-sub i)))) ; hack
      (cons x c)))
  (-->i doms d pos))

;; Make conjunctive and disjunctive contracts
(define-values (-and/c -or/c)
  (let ()
    (define (-app/c [o : Symbol] [l : Mon-Party] [es : (Listof -e)]) : -e
      (match es
        ['() 'any/c]
        [(list e) e]
        [(cons e es*)
         (-@ (-ref (-id-local o 'Λ) l (next-neg!))
             (list e (-app/c o l es*))
             (-src-loc l (next-neg!)))]))
    (values (curry -app/c 'and/c)
            (curry -app/c 'or/c))))

(: -not/c : Mon-Party -e → -e)
(define (-not/c l e)
  (-@ (-ref (-id-local 'not/c 'Λ) l (next-neg!)) (list e) (-src-loc l (next-neg!))))

(: -one-of/c : Mon-Party (Listof -e) → -e)
(define (-one-of/c l es)
  (match es
    [(list) 'none/c]
    [(list e) (-λ (list 'x₀) (-@ 'equal? (list (-x 'x₀) e) -Λ))]
    [(cons e es*)
     (-or/c l (list (-λ (list 'x₀) (-@ 'equal? (list (-x 'x₀) e) -Λ))
                    (-one-of/c l es*)))]))

(: -cons/c : -e -e → -e)
(define (-cons/c c d)
  (-struct/c -s-cons (list c d) (next-neg!)))

(: -listof : Mon-Party -e → -e)
(define (-listof l c)
  (-μ/c 'X (-or/c l (list 'null? (-cons/c c (-x/c 'X)))) (next-neg!)))

(: -box/c : -e → -e)
(define (-box/c c)
  (-struct/c -s-box (list c) (next-neg!)))

(: -list/c : (Listof -e) → -e)
(define (-list/c cs)
  (foldr -cons/c 'null? cs))

(: -list : Mon-Party (Listof -e) → -e)
(define (-list l es)
  (match es
    ['() -null]
    [(cons e es*)
     (-@ -cons (list e (-list l es*)) (-src-loc l (next-neg!)))]))

(:* -and : -e * → -e)
;; Return ast representing conjuction of 2 expressions
(define -and
  (match-lambda*
    [(list) -tt]
    [(list e) e]
    [(cons e es) (-if e (apply -and es) -ff)]))

(: -comp/c : -e -e → -e)
;; Return ast representing `(op _ e)`
(define (-comp/c op e)
  (define x 'x•)
  (-λ (list x) (-and (-@ 'real? (list (-x x)) -Λ) (-@ op (list (-x x) e) -Λ))))

(: -amb/simp : (Listof -e) → -e)
;; Smart constructor for `amb` with simplification for 1-expression case
(define -amb/simp
  (match-lambda
    [(list e) e]
    [es (-amb (list->set es))]))

(: -amb/remember : (Listof -e) → -e)
;; Return ast representing "remembered" non-determinism
(define/match (-amb/remember es)
  [((list)) -ff]
  [((list e)) e]
  [((cons e es)) (-if (•!) e (-amb/remember es))])

(: -begin/simp : (∀ (X) (Listof X) → (U X (-begin X))))
;; Smart constructor for begin, simplifying single-expression case
(define/match (-begin/simp xs)
  [((list e)) e]
  [(es) (-begin es)])

(: •! : → -•)
;; Generate new labeled hole
(define •!
  (let ([n : Natural 0])
    (λ () (begin0 (-• n) (set! n (+ 1 n))))))
