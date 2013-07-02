#lang racket
(require (only-in "../machine.rkt" ev)
         (only-in "../machine-dumb.rkt" [ev ev1])
         "../syntax.rkt")

(define verbose? #f)
(define files '())
(define TIMEOUT 300)

(command-line 
 #:once-each [("-v" "--verbose") "Verbose mode" (set! verbose? #t)]
 #:args fnames 
 (if (empty? fnames)
     (set! files (sort (map path->string (directory-list)) string<=?))
     (set! files fnames)))

(define (exec ev prog)
  (let-values ([(r t1 t2 t3) (time-apply ev (list prog))])
    (list (first r) t1 t2 t3)))

(define/match (a->time ans)
  [(#f) "-"]
  [((list (list _ t _ _))) t])

(define/match (a->blames ans)
  [(#f) "-"]
  [((list (list as _ _ _))) (for/sum ([a as] #:when (match? a `(blame ,_ ,_))) 1)])

(for ([filename files] #:when (regexp-match? #rx"sch$" filename))
  (let ([lines (length (file->lines filename))]
        [name (string-trim filename ".sch")]
        [prog (file->list filename)])
    (if verbose?
        ; only run the 'normal' evaluator for verbose mode
        (match (within-time TIMEOUT (exec ev prog))
          [#f (printf "~a: ~a lines, timeout~n~n" name lines)]
          [(list (list r t1 t2 t3))
           (printf "~a: ~a lines~ncpu time: ~a, real time: ~a, gc time: ~a~n" name lines t1 t2 t3)
           (for ([a (in-set r)]) (printf "-- ~a~n" a))
           (printf "~n")])
        ; compare with dumb-ized interpreter, dump table in latex format
        (let ([a1 (within-time TIMEOUT (exec ev prog))]
              [a2 (within-time TIMEOUT (exec ev1 prog))])
          (printf "~a & ~a & ~a / ~a & ~a / ~a\\\\~n"
                  name lines (a->time a1) (a->time a2) (a->blames a1) (a->blames a2))))))