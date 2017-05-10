#lang racket/base

;; Simple utility for searching zo structs.
;; Explores the current struct's fields recursively for a exact string match.

(provide
 ;; (-> zo String [#:limit (U Natural #f)] (Listof result))
 ;; Search a struct recursively for member zo-structs matching a string.
 zo-find
 ;; Search result: a zo-struct and the path to reach it
 (struct-out result))

(require (only-in racket/list empty?)
         (only-in racket/string string-split string-trim)
         benchmark-util
         racket/match)

(require "zo-transition.rkt"
 "zo-string.rkt"
 compiler/zo-structs)

;; -----------------------------------------------------------------------------

;; --- API functions

(struct result (z
                path)
        #:transparent)

(define (append-all xss)
  (cond [(empty? xss) '()]
        [else (append (car xss) (append-all (cdr xss)))]))

;; Searches a zo-struct `z` recursively for member zo-structs matching the `s`.
;; Terminates after at most `#:limit` recursive calls.
;; Return a list of 'result' structs.
(define (zo-find z str #:limit [lim #f])
  ;; (-> zo? string? (listof result?))
  (define-values (_ children) (parse-zo z))
  (append-all (for/list ([z*  children])
                        (zo-find-aux z* '() str 1 lim))))

;; ;; --- private functions

;; Check if `str` is one of the known looping zo-structs.
;; 2015-01-23: So far as I know, only closures may loop.
(define (may-loop? str)
  (if (member str '("closure"))
      #t #f))

;; Recursive helper for `zo-find`.
;; Add the current struct to the results, if it matches.
;; Check struct members for matches unless the search has reached its limit.
(define (zo-find-aux z hist str i lim)
  (define-values (title children) (parse-zo z))
  (define results
    (cond
     [(and lim (<= lim i))
      '()]
     ;; Terminate search if we're seeing a node for the second time
     [(and (may-loop? title) (memq z hist))
      '()]
     [else
      ;; Remember current node if we might see it again.
      (define hist* (cons z hist))
      (append-all (for/list  ([z*  children])
                              (zo-find-aux z* hist* str (add1 i) lim)))]))
  (if (and (string=? str title) (not (memq z (map result-z results))))
      (cons (result z hist) results)
      results))

;; Return the name of the zo `z` and a list of its child zo structs.
;; Uses `zo-string.rkt` to parse a raw struct.
(define (parse-zo z)
  (define z-spec     (zo->spec z))
  (define title      (car z-spec))
  (define child-strs (for/list  ([pair  (cdr z-spec)])
                               (car pair)))
  (values title (get-children z child-strs)))

;; Given a zo `z` and list of possible field names `strs`, return the list
;; of zo-structs obtained by looking up each name in `strs` in the struct `z`.
;; Relies on `zo-transition.rkt` to do the lookup.
(define (get-children z strs)
  (match strs
    ['() '()]
    [(cons hd tl)
     (define-values (r* success*) (zo-transition z hd))
     (define r r*)
     (define success? success*)
     (cond [(not success?) (get-children z tl)]
           [(list? r)      (append (filter zo? r) (get-children z tl))]
           [(zo?   r)      (cons r (get-children z tl))])]))
