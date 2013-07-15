#lang racket
(require (only-in "../machine.rkt" run)
         (only-in "../machine-dumb.rkt" [run run1])
         (only-in "../read.rkt" read-p)
         (only-in "../show.rkt" show-A show-σA)
         (only-in "../lang.rkt" checks# Blm Blm?)
         "../syntax.rkt")

(define mode 'tex)
(define files '())
(define TIMEOUT 60)

(command-line 
 #:once-each
 [("-v" "--verbose") "Verbose mode" (set! mode 'verbose)]
 [("-V" "--overbose") "Verbose+ mode with heap" (set! mode 'overbose)]
 #:args fnames 
 (if (empty? fnames)
     (set! files (sort (map path->string (directory-list)) string<=?))
     (set! files fnames)))

(define (exec run prog)
  (let-values ([(r t1 t2 t3) (time-apply run (list prog))])
    (list (first r) t1 t2 t3)))

(define/match (a->time ans)
  [(#f) "$\\infty$"]
  [((list (list _ t _ _))) t])

(define/match (a->blames ans)
  [(#f) "-"]
  [((list (list as _ _ _)))
   ; ignore error message,
   ; otherwise may get weird result where improved machine gets blamed more 
   (set-count (for/set ([a as] #:when (match? a (cons _ (? Blm?))))
                (match-let ([(cons _ (Blm l+ lo _)) a]) (cons l+ lo))))])

(define-syntax-rule (+! x v)
  (when (number? v) (set! x (+ x v))))

(when (equal? mode 'tex) (printf "Program & Lines & Checks & T1 & B1 & T2 & B2\\\\ \\hline \\hline~n"))
(define-values (L C T1 T2 B1 B2) (values 0 0 0 0 0 0))
(for ([filename files] #:when (regexp-match? #rx"sch$" filename))
  (let* ([lines (for/sum ([s (file->lines filename)] #:unless (regexp-match? #rx"^( *)(;.*)*( *)$" s)) 1)]
         [name (string-trim filename ".sch")]
         [prog (read-p (file->list filename))]
         [checks (checks# prog)])
    (match mode
      [(or 'verbose 'overbose)
       ; only run the 'normal' evaluator for verbose mode
       (match (within-time TIMEOUT (exec run prog))
         [#f (printf "~a: ~a lines, ~a checks, timeout~n~n" name lines checks)]
         [(list (list r t1 t2 t3))
          (printf "~a: ~a lines, ~a checks~ncpu time: ~a, real time: ~a, gc time: ~a~n"
                  name lines checks t1 t2 t3)
          (for ([a (in-set r)])
            (match-let ([(cons σ A) a])
              (match mode
                ['verbose (printf "-- a~n" (show-A σ A))]
                ['overbose (match-let ([(cons ans σns) (show-σA σ A)])
                             (printf "-- ~a~n   ~a~n" ans σns))])))
          (printf "~n")])]
      ['tex
       ; compare with dumb-ized interpreter, dump table in latex format
       (let ([a1 (within-time TIMEOUT (exec run prog))]
             [a2 (within-time TIMEOUT (exec run1 prog))])
         (let ([t1 (a->time a1)]
               [t2 (a->time a2)]
               [b1 (a->blames a1)]
               [b2 (a->blames a2)])
           (+! L lines) (+! C checks)
           (+! T1 t1) (+! T2 t2) (+! B1 b1) (+! B2 b2)
           (printf "~a & ~a & ~a & ~a & ~a & ~a & ~a\\\\~n" name lines checks t1 b1 t2 b2)))])))
(when (equal? mode 'tex)
  (begin
    (printf "\\hline~n")
    (printf "TOTAL & ~a & ~a & ~a & ~a & ~a & ~a~n" L C T1 B1 T2 B2)))