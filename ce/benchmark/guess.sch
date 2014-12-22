(module IO racket
  (provide/contract
   [display (string? . -> . any/c)]
   [error (string? . -> . any/c)]
   [read (-> any/c)]))

(module guess racket
  (provide/contract [guess (integer? . -> . any/c)])
  (require (submod ".." IO))
  (define (guess target)
    (let ([input (read)])
      (cond
        [(not (or (equal? input 'quit) (integer? input)))
         (error "Invalid type for input")]
        [(equal? input 'quit) 'quit]
        [(< input target)
         (begin (display "Too low!\n") (guess target))]
        [(> input target)
         (begin (display "Too high!\n") (guess target))]
        [else (begin (display "Correct!\n") 'done)]))))

(require 'guess)
(guess •)
