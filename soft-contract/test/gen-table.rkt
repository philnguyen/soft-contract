#lang typed/racket

(require set-extras
         "../utils/main.rkt"
         "../ast/signatures.rkt"
         "../runtime/signatures.rkt"
         "../main.rkt"
         "count-checks.rkt")

(require/typed srfi/13
  [string-pad-right (String Natural → String)])

(define TIMEOUT (* 60 60))
(define COLUMNS '(Lines All-checks Explicit-checks Time Positives))
(define COL-PROGRAM-WIDTH 20)
(define sep "|" #;"&")
(define end "" #;"\\\\")
(define header-end "" #;"\\hline ")

(define (col-width [c : Symbol]) (max 7 (add1 (string-length (symbol->string c)))))

(define (pad s [w : Natural]) (string-pad-right (format "~a" s) w))

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
  (define-values (all-checks explicit-checks)
    (match-let ([stats (count-checks (parse-files (list p)))])
      ;(printf "~a~n" stats)
      (values (hash-ref stats 'total)
              (hash-ref stats 'leaf (λ () 0)))))

  (: count-poses : → Real/Rng)
  (define (count-poses)
    (match (with-time-limit : Natural TIMEOUT
             (define-values (As _) (havoc-files (list p)))
             (set-count
              ;; Same location means same contract,
              ;; But include contract due to inaccurate location from `fake-contract`
              (for/seteq: : (℘ ℓ) ([A (in-set As)] #:when (-blm? A))
                (match-define (-blm l+ lo Cs Vs ℓ) A)
                ℓ)))
      [(list n) n]
      [#f (list all-checks)]))

  (collect-garbage) (collect-garbage) (collect-garbage)
  (match-define-values ((list poses) t t-real t-gc) (time-apply count-poses '()))
  
  (Row name (hash-set
             ((inst hash Symbol Real/Rng)
              'Lines lines
              'All-checks all-checks 
              'Time (exact->inexact (/ t 1000))
              'Positives poses)
             'Explicit-checks explicit-checks)))

(define (print-then-return-row [row : Row]) : Row
  (match-define (Row name fields) row)
  (display (pad name COL-PROGRAM-WIDTH))
  (for ([col (in-list COLUMNS)])
    (printf "~a " sep)
    (display (pad (show-Real/Rng (hash-ref fields col)) (col-width col))))
  (printf "~a~n" end)
  row)

(define (print-header)
  (display (pad "Program" COL-PROGRAM-WIDTH))
  (for ([col (in-list COLUMNS)])
    (printf "~a " sep)
    (display (pad col (col-width col))))
  (printf "~a ~a~n" end header-end))

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

