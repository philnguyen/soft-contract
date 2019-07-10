#lang racket

(define x (file->lines "hihi.txt"))

(provide
 (contract-out
  [x (listof string?)]))
