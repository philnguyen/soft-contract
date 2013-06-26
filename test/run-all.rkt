#lang racket
(require "../machine.rkt" "../syntax.rkt")

(define verbose? #f)
(define files '())

(command-line 
 #:once-each [("-v" "--verbose") "Verbose mode" (set! verbose? #t)]
 #:args fnames 
 (if (empty? fnames)
     (set! files (sort (map path->string (directory-list)) string<=?))
     (set! files fnames)))

(define (exec prog)
  (let-values ([(r t1 t2 t3) (time-apply ev (list prog))])
    (list (first r) t1 t2 t3)))

(for ([filename files]
      #:when (regexp-match? #rx"sch$" filename))
  (let ([lines (length (file->lines filename))]
        [name (string-trim filename ".sch")]
        [prog (file->list filename)])
    (match (within-time 60 (exec prog))
      [#f (if verbose? (printf "~a: ~a lines, timeout~n~n" name lines)
              (printf "~a & ~a & - & -\\\\~n" name lines))]
      [(list (list r t1 t2 t3))
       (if verbose?
           (begin
             (printf "~a: ~a lines~ncpu time: ~a, real time: ~a, gc time: ~a~n"
                     name lines t1 t2 t3)
             (for ([a (in-set r)]) (printf "-- ~a~n" a))
             (printf "~n"))
           (let ([blames (for/sum ([ri r] #:when (match? ri `(blame ,_ ,_))) 1)])
             (printf "~a & ~a & ~a & ~a\\\\~n" name lines t1 blames)))])))