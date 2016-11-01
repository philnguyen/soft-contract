#lang typed/racket

(require "../utils/set.rkt"
         "../runtime/definition.rkt"
         "../reduction/quick-step.rkt")

(struct Res ([name : String]
             [lines : Natural]
             [checks : Natural]
             [time : Natural]
             [poses : Natural])
  #:transparent)

(: run-file : Path → Res)
(define (run-file fn)
  (collect-garbage) (collect-garbage) (collect-garbage)
  (define t₀ (current-milliseconds))
  (define-values (As _) (havoc-file (path->string fn)))
  (define δt (- (current-milliseconds) t₀))
  
  (define-values (_init fn.rkt _flag) (split-path fn))
  (Res (format "~a" (path-replace-extension (cast fn.rkt Path-For-Some-System) ""))
       (count-lines fn)
       (count-checks fn)
       (assert δt exact-nonnegative-integer?)
       (count-poses As)))

(: run-dir : (U Path Path-String) → (Values (Listof Res) Res))
(define (run-dir dir)
  (cond
    [(string? dir)
     (run-dir (string->path dir))]
    [else
     (define reses : (Listof Res)
       (for/list ([fn (in-directory dir)])
         (run-file fn)))
     (define res
       (let-values ([(Σ-lines Σ-checks Σ-time Σ-poses)
                     (for/fold ([Σ-lines : Natural 0]
                                [Σ-checks : Natural 0]
                                [Σ-time : Natural 0]
                                [Σ-poses : Natural 0])
                               ([res reses])
                       (match-define (Res _ lines checks time poses) res)
                       (values (+ Σ-lines lines)
                               (+ Σ-checks checks)
                               (+ Σ-time time)
                               (+ Σ-poses poses)))])
         (define-values (_init dir-name _) (split-path dir))
         (Res "TOTAL" #;(format "~a" dir-name)
              Σ-lines
              Σ-checks
              Σ-time
              Σ-poses)))
     (values reses res)]))

(: Res->latex-row : Res → String)
(define (Res->latex-row res)
  (match-define (Res name lines checks time poses) res)
  (cond
    [(zero? poses)
     (format "~a & ~a & ~a & ~a \\\\" name lines checks time)]
    [else
     (format "~a & ~a & ~a & ~a (~a) \\\\" name lines checks time poses)]))

(: Reses->latex-table : (Listof Res) Res → String)
(define (Reses->latex-table reses res)
  (string-join
   `("Program & Lines & Checks & Time in ms \\\\"
     ,@(for/list : (Listof String) ([res reses])
         (Res->latex-row res))
     "\\hline \\\\"
     ,(Res->latex-row res))
   "\n"))

(: count-lines : Path → Natural)
(define (count-lines fn)
  #|TODO|#
  0)

(: count-checks : Path → Natural)
(define (count-checks p)
  #|TODO|#
  0)

(: count-poses : (℘ -ΓA) → Natural)
(define (count-poses ΓAs)
  (for/sum : Natural ([ΓA ΓAs])
    (match-define (-ΓA _ A) ΓA)
    (if (-blm? A) 1 0)))
