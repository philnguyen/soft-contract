#lang soft-contract

;; Adapted from example 14 in LTUL
(module f racket
  (provide
   (contract-out
    [f ((or/c number? string?) cons? . -> . number?)]))
  (define (f input extra)
    (cond
     [(and (number? input) (number? (car extra)))
      (+ input (car extra))]
     [(number? (car extra))
      (+ (string-length input) (car extra))]
     [else 0])))
