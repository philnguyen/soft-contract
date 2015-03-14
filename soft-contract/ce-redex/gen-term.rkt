#lang racket/base
(provide gen gen/T +L!)
(require redex/reduction-semantics racket/contract racket/function racket/contract racket/match
         "lib.rkt" "lang.rkt" "tc.rkt")

(define/contract (gen/T T [max-depth 2] [inst? #f])
  ([T?] [(and/c integer? (>=/c 0)) boolean?] . ->* . (listof E?))
  (cond [inst? (parameterize ([opq-rate 0])
                 (judgment-holds (gen-V ,T ,max-depth E) E))]
        [else (judgment-holds (gen {} ,T ,max-depth E) E)]))

(define/contract opq-rate
  (parameter/c (and/c (>=/c 0) (</c 1)))
  (make-parameter 0.5))

;; Generate terms of type `T` with max depth `n` and free variables in `Γ`
;; The `(prob _)` guards are to randomly truncate some of the branches
(define-judgment-form SCPCF
  #:contract (gen Γ T n E)
  #:mode     (gen I I I O)
  ;; Depth 0
  [(side-condition ,(prob 0.5))
   -----------------------------------------------
   (gen Γ ℤ 0 ,(random-ℤ))]
  [(side-condition ,(prob (opq-rate)))
   -----------------------------------------------
   (gen Γ T 0 (• T ,(+L!)))]
  [(where {_ ... [X ↦ T] _ ...} Γ)
   -----------------------------------------------
   (gen Γ T 0 X)]
  ;; Function
  [(where X (Γ! Γ T_x))
   (gen (++ Γ [X ↦ T_x]) T_y n E)
   -----------------------------------------------
   (gen Γ (T_x → T_y) n (λ (X : T_x) E))]
  ;; Depth 1+n
  ; Decrease depth
  [(gen Γ T ,(- (term n+) 1) E)
   -----------------------------------------------
   (gen Γ T n+ E)]
  ; Conditional
  [(side-condition ,(prob 0.2))
   (where n_1 ,(random (term n+)))
   (gen Γ ℤ ,(random (term n+)) E_1)
   (gen Γ T ,(random (term n+)) E_2)
   (gen Γ T ,(random (term n+)) E_3)
   -----------------------------------------------
   (gen Γ T n+ (if E_1 E_2 E_3))]
  ; Application
  [(side-condition ,(prob 0.2))
   (where n_1 ,(random (term n+)))
   (where T_x ,(generate-term SCPCF T (term n_1)))
   (gen Γ (T_x → T) n_1 E_f)
   (gen Γ T_x n_1 E_x)
   -----------------------------------------------
   (gen Γ T n+ (E_f E_x))]
  ; Primitive application
  [(side-condition ,(prob 0.2))
   (gen Γ ℤ ,(random (term n+)) E)
   (where O¹ ,(random-O¹))
   -----------------------------------------------
   (gen Γ ℤ n+ (O¹ E ,(+L!)))]
  [(side-condition ,(prob 0.2))
   (gen Γ ℤ ,(random (term n+)) E_1)
   (gen Γ ℤ ,(random (term n+)) E_2)
   (where O² ,(random-O²))
   -----------------------------------------------
   (gen Γ ℤ n+ (O² E_1 E_2 ,(+L!)))])

(define-judgment-form SCPCF
  #:contract (gen-V T n E)
  #:mode     (gen-V I I O)
  [(gen-V ℤ _ ,(random-ℤ))]
  [(where X (Γ! {} T′))
   (gen {[X ↦ T′]} T n E)
   -----------------------------------------------
   (gen-V (T′ → T) n (λ (X : T′) E))])

;; Just because `judgment-form` complains about unknown pattern
(define (random-O¹) (generate-term SCPCF O¹ 0))
(define (random-O²) (generate-term SCPCF O² 0))

;; random int, favor 0 a little bit
(define (random-ℤ) (if (prob 0.3) 0 (random 100)))

;; Return fresh variable not in environment
(define-metafunction SCPCF
  Γ! : Γ T -> X
  [(Γ! Γ ℤ) ,(variable-not-in (term Γ) 'n)]
  [(Γ! Γ (ℤ → ℤ)) ,(variable-not-in (term Γ) 'f)]
  [(Γ! Γ _) ,(variable-not-in (term Γ) 'g)])

(define +L!
  (let ([n 0])
    (λ () (begin0 (string->symbol (format "L~a" n))
            (set! n (+ 1 n))))))

(define/contract (prob r)
  ((and/c (>=/c 0) (</c 1)) . -> . boolean?)
  (<= (random) r))

(module+ test

  (redex-check ; randomly generated term has the right type
   SCPCF T
   (begin
     (define Es (gen/T (term T)))
     (printf "Typechecking ~a random terms for ~a~n" (length Es) (term T))
     (for/and ([E (in-list Es)])
       (test-equal (term (tc ,E)) (term T))))
   #:attempts 50))
