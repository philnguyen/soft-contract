#lang racket
(require "../machine.rkt")

(for ([filename (sort (map path->string (directory-list)) string<=?)]
      #:when (regexp-match? #rx"sch$" filename))
  (let ([lines# (with-input-from-file filename
                  (thunk (length (port->lines (current-input-port)))))])
    (with-input-from-file filename
      (thunk
       (let ([prog (for/list ([form (in-port read)]) form)])
         (printf "~a: ~a lines~n" filename lines#)
         (let ([ans (time (ev prog))])
           (for ([a ans]) (printf "-- ~a~n" a)))
         (printf "~n"))))))