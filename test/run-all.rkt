#lang racket
(require (only-in "../machine.rkt" run)
         (only-in "../machine-dumb.rkt" [run run1])
         (only-in "../read.rkt" read-p)
         (only-in "../lang.rkt" checks#)
         "../syntax.rkt")

(define verbose? #f)
(define files '())
(define TIMEOUT 60)

(command-line 
 #:once-each [("-v" "--verbose") "Verbose mode" (set! verbose? #t)]
 #:args fnames 
 (if (empty? fnames)
     (set! files (sort (map path->string (directory-list)) string<=?))
     (set! files fnames)))

(define (exec run prog)
  (let-values ([(r t1 t2 t3) (time-apply run (list prog))])
    (list (first r) t1 t2 t3)))

(define/match (a->time ans)
  [(#f) "-"]
  [((list (list _ t _ _))) t])

(define/match (a->blames ans)
  [(#f) "-"]
  [((list (list as _ _ _)))
   ; ignore error message,
   ; otherwise may get weird result where improved machine gets blamed more 
   (set-count (for/set ([a as] #:when (match? a `(blame ,_ ...)))
                (match-let ([(list _ l+ lo _) a]) (cons l+ lo))))])

(unless verbose? (printf "Program & Lines & Checks & Time (ms) & False Blames\\\\ \\hline \\hline~n"))
(for ([filename files] #:when (regexp-match? #rx"sch$" filename))
  (let* ([lines (for/sum ([s (file->lines filename)] #:unless (regexp-match? #rx"^( *)(;.*)*( *)$" s)) 1)]
         [name (string-trim filename ".sch")]
         [prog (read-p (file->list filename))]
         [checks (checks# prog)])
    (if verbose?
        ; only run the 'normal' evaluator for verbose mode
        (match (within-time TIMEOUT (exec run prog))
          [#f (printf "~a: ~a lines, ~a checks, timeout~n~n" name lines checks)]
          [(list (list r t1 t2 t3))
           (printf "~a: ~a lines, ~a checks~ncpu time: ~a, real time: ~a, gc time: ~a~n" name lines checks t1 t2 t3)
           (for ([a (in-set r)]) (printf "-- ~a~n" a))
           (printf "~n")])
        ; compare with dumb-ized interpreter, dump table in latex format
        (let ([a1 (within-time TIMEOUT (exec run prog))]
              [a2 (within-time TIMEOUT (exec run1 prog))])
          (printf "~a & ~a & ~a & ~a / ~a & ~a / ~a\\\\~n"
                  name lines checks (a->time a1) (a->time a2) (a->blames a1) (a->blames a2))))))