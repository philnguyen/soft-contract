#lang racket

(define (run-it i name thunk-safe thunk-unsafe)
  (define (bench f)
    (for/sum ([j (in-range i)])
      (collect-garbage)
      (collect-garbage)
      (define-values (res cpu real gc)
        (time-apply f empty))
      cpu))
  
  (define con (bench thunk-safe))
  (define ver (bench thunk-unsafe))
  (printf "~a~n" name)
  (printf "contract (~a runs): ~a~n" i con)
  (printf "verified (~a runs): ~a~n" i ver)
  (printf "speedup:            ~a~n" (* 1. (/ con ver))))

(require (prefix-in z: "zombie.rkt"))
(require (prefix-in s: "snake.rkt"))

(define z:h (reverse (with-input-from-file "zombie-hist-4.txt" read)))
(define s:h (reverse (with-input-from-file "snake-hist-2.txt" read)))

(run-it 50
        'zombie
        (λ () (z:replay z:w1 z:h))
        (λ () (z:replay z:unsafe:w1 z:h)))

(run-it 50
        'snake
        (λ () (s:replay s:w0 s:h))
        (λ () (s:unsafe:replay s:unsafe:w0 s:h)))
