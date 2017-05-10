#lang racket/base

(provide forth-eval*)

;; -----------------------------------------------------------------------------

(require
  racket/match
  racket/class
  (only-in racket/port with-input-from-string)
)
(require (only-in "command.rkt"
  CMD*
  command%
))
(require (only-in "stack.rkt"
  stack-init
))

(define (assert v p)
  (unless (p v) (error 'assert))
  v)

;; =============================================================================

(define defn-command
  (new command%
    (id 'define)
    (descr "Define a new command as a sequence of existing commands")
    (exec (lambda (E S v)
      (match v
       [(cons (or ': 'define) (cons w defn*-any))
        (define defn* (assert defn*-any list?))
        (define cmd
          (new command%
            (id (assert w symbol?))
            (descr (format "~a" defn*))
            (exec (lambda (E S v)
              (if (equal? v (list w))
                  (let-values ([(e+ s+)
                                (for/fold
                                    ([e E] [s S])
                                    ([d (in-list defn*)])
                                  (if e
                                    (forth-eval e s (list d))
                                    (values e s)))])
                    (if e+
                      (cons e+ s+)
                      e+))
                  #f)))))
        (cons (cons cmd E) S)]
       [_ #f])))))

(define (forth-eval* in)
  (for/fold
            ([e (cons defn-command CMD*)]
             [s (stack-init)])
      ([ln (in-lines in)])
    (define token* (forth-tokenize ln))
    (cond
     [(or (null? token*)
          (not (list? e))) ;; Cheap way to detect EXIT
      (values '() s)]
     [else
      (forth-eval e s token*)])))

(define (forth-eval E S token*)
  (match (for/or
                 ([c (in-list E)]) ((get-field exec c) E S token*))
    ['EXIT
     (values #f S)]
    [#f
     (printf "Unrecognized command '~a'.\n" token*)
     (values E S)]
    [(? pair? E+S)
     (values (car E+S) (cdr E+S))]))

(define (forth-tokenize str)
  (parameterize ([read-case-sensitive #f]) ;; Converts symbols to lowercase
    (with-input-from-string str
      (lambda ()
        (de-nest
         (let loop ()
           (match (read)
             [(? eof-object?) '()]
             [val (cons val (loop))])))))))

;; Remove all parentheses around a singleton list
(define (de-nest v*)
  (if (and (list? v*)
           (not (null? v*))
           (list? (car v*))
           (null? (cdr v*)))
      (de-nest (car v*))
      v*))

