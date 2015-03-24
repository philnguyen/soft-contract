#lang racket/base
(provide (all-defined-out))
(require
 redex/reduction-semantics racket/match racket/port racket/system racket/string racket/function
 "lib.rkt" "lang.rkt" "tc.rkt" "proof-system.rkt")

(define-metafunction SCPCF
  translate-Σ : Σ -> (any ...)
  [(translate-Σ {[L ↦ S] ...})
   (φ ... ...)
   (where ((φ ...) ...) ((assert-L-S L S) ...))])

(define-metafunction SCPCF
  declare-Σ : Σ -> (decl ...)
  [(declare-Σ {[L ↦ S] ...})
   ,(filter values (term ((declare (ℓ L) (tc-S S)) ...)))])

(define-metafunction SCPCF
  assert-L-S : L S -> (φ ...)
  [(assert-L-S L n) {(= (ℓ L) n)}]
  [(assert-L-S L (• ℤ P ...))
   ,(filter values (term ((assert-L-P L P) ...)))]
  [(assert-L-S L (case ℤ any ...))
   ,(let loopₗ ([left (term (any ...))])
      (match left
        [(or '() (list _)) '()]
        [(cons `(,L₁ ↦ ,L₂) left*)
         (append
          (let loopᵣ ([right left*])
            (match right
              ['() '()]
              [(cons `(,L₃ ↦ ,L₄) right*)
               (cons (term (implies (= (ℓ ,L₁) (ℓ ,L₃)) (= (ℓ ,L₂) (ℓ ,L₄))))
                     (loopᵣ right*))]))
          (loopₗ left*))]))]
  [(assert-L-S _ _) {}])

(define-metafunction SCPCF
  assert-L-P : L P -> φ or #f
  [(assert-L-P L (λ (X : ℤ) (zero? X _))) (= (ℓ L) 0)]
  [(assert-L-P L (λ (X : ℤ) (= X (O² E ... _) _)))
   (= (ℓ L) ((⦃O⦄ O²) (⦃E⦄ E) ...))]
  [(assert-L-P L (λ (X : ℤ) (O² X E _))) ((⦃O⦄ O²) (ℓ L) (⦃E⦄ E))]
  [(assert-L-P L P) #f
   (side-condition (printf "ignore translation of ~a to Z3~n" (term P)))])

(define-metafunction SCPCF
  ℓ : L -> X
  [(ℓ L) ,(string->symbol (format "L-~a" (term L)))])

(define-metafunction SCPCF
  →L : X -> L
  [(→L X) ,(match (symbol->string (term X))
             [(regexp #rx"L-(.+)" (list _ (? string? s))) (string->number s)])])

(define-metafunction SCPCF
  ⦃E⦄ : E -> t
  [(⦃E⦄ n) n]
  [(⦃E⦄ (↓ ℤ L)) (ℓ L)])

(define-metafunction SCPCF
  ⦃O⦄ : O -> any
  [(⦃O⦄ ≥) >=]
  [(⦃O⦄ ≤) <=]
  [(⦃O⦄ O²) O²])

(define-metafunction SCPCF
  declare : X T -> decl or #f
  [(declare X ℤ) (declare-const X Int)]
  [(declare X (ℤ → ℤ)) (declare-fun X (Int) Int)]
  [(declare _ _) #f])

(define-metafunction SCPCF
  query : (decl ...) (φ ...) φ -> R
  [(query (decl ...) (φ ...) ψ) ✓
   (side-condition
    (regexp-match? #rx"^unsat" (term (call (decl ... (assert φ) ... (assert (not ψ)) (check-sat))))))]
  [(query (decl ...) (φ ...) ψ) !
   (side-condition
    (regexp-match? #rx"^unsat" (term (call (decl ... (assert φ) ... (assert ψ) (check-sat))))))]
  [(query _ _ _) ?])

(define-metafunction SCPCF
  call : (any ...) -> string
  [(call (any ...))
   ,(let ()
      (define req (string-join (map (curry format "~a") (term (any ...))) "\n"))
      (define res
        (with-output-to-string
          (λ () (system (format "echo \"~a\" | z3 -in -smt2" req)))))
      (log-debug "call:~n~a~nres:~n~a~n" req res)
      res)])

(define-metafunction SCPCF
  query/model : Σ -> (any ...)
  [(query/model (name Σ {[L ↦ S] ...}))
   (decl ... (assert φ) ... ... (check-sat) (get-model))
   (where (decl ...) (declare-Σ Σ))
   (where ((φ ...) ...) ((assert-L-S L S) ...))])

(define-metafunction SCPCF
  model/z3 : Σ -> Σ or #f
  [(model/z3 Σ)
   ,(match (term (call (query/model Σ)))
      [(regexp #rx"^sat(.*)" (list _ (? string? s)))
       (match (with-input-from-string s read)
         [(list 'model lines ...)
          (for/fold ([Σ (term Σ)]) ([line (in-list lines)])
            (match-define `(define-fun ,(? symbol? L) () ,_ ,e) line)
            (term (!! ,Σ [(→L ,L) ↦ ,(eval e)])))])]
      [_ #f])])

(define-metafunction SCPCF
  model/Σ : Σ -> Σ
  [(model/Σ (name Σ {[L ↦ _] ...})) {[L ↦ (inst/L Σ L)] ...}])

(define-metafunction SCPCF
  inst/L : Σ L -> S
  [(inst/L (name Σ {_ ... [L ↦ (• ℤ P ...)] _ ...}) L)
   (inst/n 0 Σ L)]
  [(inst/L Σ L) (@ Σ L)])

(define-metafunction SCPCF
  inst/n : n Σ L -> n
  [(inst/n n Σ L) n
   (where #f (refutes Σ L (λ (x : ℤ) (= x n Λ))))]
  [(inst/n n Σ L) n_1
   (where #t (refutes Σ L (λ (x : ℤ) (= x n Λ))))
   (where n_1 ,(- (random 2000) 1000))])

(module+ test
  (require rackunit)
  (define-term Σ
    {[0 ↦ 1]
     [1 ↦ (• ℤ (λ (x : ℤ) (< x 3 Λ)))]
     [2 ↦ (• ℤ (λ (x : ℤ) (= x (+ (↓ ℤ 0) (↓ ℤ 1) Λ) Λ)))]
     [3 ↦ 42]
     [4 ↦ (case ℤ [0 ↦ 1] [2 ↦ 3])]})
  (term (declare-Σ Σ))
  (term (translate-Σ Σ)))
