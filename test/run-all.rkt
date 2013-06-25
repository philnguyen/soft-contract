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

(for ([filename files]
      #:when (regexp-match? #rx"sch$" filename))
  (let ([lines (length (file->lines filename))]
        [name (string-trim filename ".sch")]
        [prog (file->list filename)])
    (if verbose?
        (begin
          (printf "~a: ~a lines~n" name lines)
          (for ([a (time (ev prog))]) (printf "-- ~a~n" a))
          (printf "~n"))
        (let-values ([(r time _1 _2) (time-apply ev (list prog))])
          (let ([blames (for/sum ([ri (in-set (first r))]
                                  #:when (match? ri `(blame ,_ ,_))) 1)])
            (printf "~a & ~a & ~a & ~a\\\\~n" name lines time blames))))))