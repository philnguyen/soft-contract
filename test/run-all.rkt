#lang racket
(require "../machine.rkt")

(for ([filename
       ; commandline parameters as files to run. Run all by default.
       (match (current-command-line-arguments)
         [(vector) (sort (map path->string (directory-list)) string<=?)]
         [names names])]
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