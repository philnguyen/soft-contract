#lang racket

(define (run-it i name thunk-safe thunk-unsafe)
  (define (bench f)
    (collect-garbage)
    (collect-garbage)
    (define-values (res cpu real gc) 
      (time-apply (lambda ()
		    (for ([j (in-range i)])
			 (f)))
		  empty))
    cpu)
      
  (define con (bench thunk-safe))
  (define ver (bench thunk-unsafe))
  (printf "~a~n" name)
  (printf "contract (~a runs): ~a~n" i con)
  (printf "verified (~a runs): ~a~n" i ver)
  (printf "speedup:            ~a~n" (* 1. (/ con ver))))

(require (prefix-in z: "zombie.rkt"))
(require (prefix-in s: "snake.rkt"))
(require (prefix-in t: "tetris.rkt"))

(define z:h (reverse (with-input-from-file "zombie-hist-4.txt" read)))
(define s:h (reverse (with-input-from-file "snake-hist-2.txt" read)))
(define t:h (reverse (with-input-from-file "tetris-hist-1.txt" read)))
(define t:h2 (reverse (with-input-from-file "tetris-hist-2.txt" read)))
(define t:h3 (reverse (with-input-from-file "tetris-hist-3.txt" read)))

(run-it 50
        'zombie
        (λ () (z:replay z:w1 z:h))
        (λ () (z:replay z:unsafe:w1 z:h)))

(run-it 50
        'snake
        (λ () (s:replay s:w0 s:h))
        (λ () (s:unsafe:replay s:unsafe:w0 s:h)))

(run-it 1 ; something is super expensive...
        'tetris
        (λ () (t:replay t:w0 t:h3))
        (λ () (t:unsafe:replay t:unsafe:w0 t:h3)))

(provide (all-defined-out))
