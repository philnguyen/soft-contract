#lang typed/racket

(require set-extras
         "../utils/main.rkt"
         "../ast/signatures.rkt"
         "../runtime/signatures.rkt"
         "../main.rkt"
         "count-checks.rkt")

(define TIMEOUT (* 60 20))
(define COLUMNS '(Lines Checks Time Pos))

(define-type Real/Rng (U Real (List Real)))
(define-type Record (HashTable Symbol Real/Rng))

(: Real/Rng+ : Real/Rng Real/Rng → Real/Rng)
(define Real/Rng+
  (match-lambda**
   [((? real? n₁) (? real? n₂)) (+ n₁ n₂)]
   [((or (list n₁) (? real? n₁)) (or (list n₂) (? real? n₂))) #:when (and n₁ n₂)
    (list (+ n₁ n₂))]))

(define show-Real/Rng : (Real/Rng → String)
  (match-lambda
    [(? real? n) (number->string n)]
    [(list n) (format "(~a, ∞)" n)]))

(struct Row ([name : String] [attrs : Record]) #:transparent)

(: Row+ : String (Listof Symbol) (Listof Row) → Row)
(define (Row+ name keys rows)
  (define fields
    (for*/fold ([fields : Record (hasheq)])
               ([row (in-list rows)]
                [fieldsᵢ (in-value (Row-attrs row))]
                [key (in-list keys)])
      (hash-update fields key
                   (λ ([x : Real/Rng])
                     (Real/Rng+ x (hash-ref fieldsᵢ key))) (λ () 0))))
  (Row name fields))

(: count-lines : Path-String → Natural)
(define (count-lines p)
  (define (empty-line? [l : String]) ; ignore lines that are empty or pure comment
    (or (regexp-match? #rx"^ *;.*$" l)
        (regexp-match? #rx"^ *$" l)))
  (for/sum : Natural ([l (file->lines p)] #:unless (empty-line? l)) 1))

(: run-file : Path-String → Row)
(define (run-file p)
  (define name
    (match-let ([(? path-for-some-system? p) (last (explode-path p))]) 
      (some-system-path->string (path-replace-extension p ""))))
  (define lines (count-lines p))
  (define checks
    (match-let ([stats (count-checks (parse-files (list p)))])
      ;(printf "~a~n" stats)
      (hash-ref stats 'total)))

  (: count-poses : → Real/Rng)
  (define (count-poses)
    (match (with-time-limit : Natural TIMEOUT
             (define-values (As _) (havoc-files (list p)))
             (set-count
              ;; Same location means same contract,
              ;; But include contract due to inaccurate location from `fake-contract`
              (for/seteq: : (℘ ℓ) ([ΓA (in-set As)] #:when (-blm? (-ΓA-ans ΓA)))
                (match-define (-blm l+ lo Cs Vs ℓ) (-ΓA-ans ΓA))
                ℓ)))
      [(list n) n]
      [#f (list checks)]))

  (collect-garbage) (collect-garbage) (collect-garbage)
  (match-define-values ((list poses) t t-real t-gc) (time-apply count-poses '()))
  
  (Row name ((inst hasheq Symbol Real/Rng)
             'Lines lines
             'Checks checks
             'Time (exact->inexact (/ t 1000))
             'Pos poses)))

(define (print-then-return-row [row : Row]) : Row
  (match-define (Row name fields) row)
  (printf "\\textrm{~a} " name)
  (for ([col (in-list COLUMNS)])
    (printf "& ~a " (show-Real/Rng (hash-ref fields col))))
  (printf "\\\\~n")
  row)

(define (print-header)
  (printf "Program ")
  (for ([col (in-list COLUMNS)])
    (printf "& ~a " col))
  (printf "\\\\ \\hline~n"))

(: run-dir : Path-String → (Values (Listof Row) Row))
;; Run each file and print along the way
(define (run-dir dir)
  (print-header)
  (define rows ; with side effect printing row
    (for*/list : (Listof Row) ([fp (in-list (directory-list dir))]
                               [fn (in-value (path->string fp))]
                               #:when (regexp-match-exact? #rx".*rkt" fn))
      (print-then-return-row (run-file (build-path dir fn)))))
  (define sum-row (print-then-return-row (Row+ "TOTAL" COLUMNS rows)))
  (values rows sum-row))

(command-line
   #:args paths
   (for ([path (in-list paths)])
     (assert path path-string?)
     (cond [(directory-exists?              path)
            (run-dir path)]
           [(regexp-match-exact? #rx".*rkt" path)
            (print-then-return-row (run-file path))]
           [else (printf "Don't know what path ~a means" path)])
     (printf "~n")))

