#lang racket

(struct posn (x) #:transparent)

(provide
 (contract-out
  [struct posn ([x real?])]))
