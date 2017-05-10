#lang racket/base

(provide
  enqueue-message!
  reset-message-queue!
)


;; list of strings (messages) which were produced since the previous
;; previous display, and need to be displayed now
(define message-queue '())

(define (enqueue-message! m)
  (set! message-queue (cons m message-queue)))

(define (reset-message-queue!)
  (set! message-queue '()))
