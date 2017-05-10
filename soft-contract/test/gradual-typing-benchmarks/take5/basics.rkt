#lang racket/base

;; basic constants and types for the game

(provide
 ;; constants 
 FACE
 HAND
 SIXTYSIX
 STACKS
 FIVE
 MAX-BULL
 MIN-BULL
 ;; -> [Listof Number]
 configuration)

;; -----------------------------------------------------------------------------

(define FACE 104)
(define HAND 10)
(define SIXTYSIX 66)
(define STACKS 4)
(define FIVE 5)
(define MAX-BULL 7)
(define MIN-BULL 2)

(define (configuration)
  `((FACE     ,FACE)
    (HAND     ,HAND)
    (SIXTSIX  ,SIXTYSIX)
    (STACKS   ,STACKS)
    (FIVE     ,FIVE)
    (MAX_BULL ,MAX-BULL)
    (MIN_BULL ,MIN-BULL)))

