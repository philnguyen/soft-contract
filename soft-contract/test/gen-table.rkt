#lang typed/racket

(require "../utils/main.rkt"
         "../ast/main.rkt"
         "../runtime/main.rkt"
         "../parse/main.rkt"
         "../run.rkt")

(define TIMEOUT (* 60 20))
(define COLUMNS '(Lines Checks Time Positives))

(define-type Nat/Rng (U Natural (List Natural)))
(define-type Record (HashTable Symbol Nat/Rng))

(: Nat/Rng+ : Nat/Rng Nat/Rng → Nat/Rng)
(define Nat/Rng+
  (match-lambda**
   [((? integer? n₁) (? integer? n₂)) (+ n₁ n₂)]
   [((or (list n₁) (? integer? n₁)) (or (list n₂) (? integer? n₂))) #:when (and n₁ n₂)
    (list (+ n₁ n₂))]))

(define show-Nat/Rng : (Nat/Rng → String)
  (match-lambda
    [(? integer? n) (number->string n)]
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
                   (λ ([x : Nat/Rng])
                     (Nat/Rng+ x (hash-ref fieldsᵢ key))) (λ () 0))))
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
  (define checks (checks# (file->module p)))

  (: count-poses : → Nat/Rng)
  (define (count-poses)
    (match (with-time-limit : Natural TIMEOUT
             #;(define-values (As _) (havoc-file p))
             #;(for/sum : Natural ([ΓA (in-set As)])
               (if (-blm? (-ΓA-ans ΓA)) 1 0))
             0)
      [(list n) n]
      [#f (list TIMEOUT)]))

  (collect-garbage) (collect-garbage) (collect-garbage)
  (match-define-values ((list poses) t t-real t-gc) (time-apply count-poses '()))
  
  (Row name ((inst hasheq Symbol Nat/Rng)
             'Lines lines
             'Checks checks
             'Time t
             'Positives poses)))

(define (print-then-return-row [row : Row]) : Row
  (match-define (Row name fields) row)
  (printf "\\textrm{~a} " name)
  (for ([col (in-list COLUMNS)])
    (printf "& ~a " (show-Nat/Rng (hash-ref fields col))))
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
  (define rows : (Listof Row) ; with side effect printing row
    (for*/list ([fp (in-list (directory-list dir))]
                [fn (in-value (path->string fp))]
                #:when (regexp-match-exact? #rx".*rkt" fn))
      (print-then-return-row (run-file (build-path dir fn)))))
  (define sum-row (print-then-return-row (Row+ "TOTAL" COLUMNS rows)))
  (values rows sum-row))

(command-line
   #:args dirs
   (for ([dir (in-list dirs)])
     (run-dir (assert dir path-string?))
     (printf "~n")))

