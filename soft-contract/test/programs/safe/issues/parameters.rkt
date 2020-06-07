#lang racket/base

(require racket/contract)

(define x (make-parameter 42))
(define y (make-parameter "hi"))

(define z (parameterize ([x (+ (x) 1)]
                         [y (string-length (y))])
            (+ (x) 2 (y))))

(provide
 (contract-out
  [x (-> exact-integer?)]
  [y (-> string?)]
  [z exact-integer?]))
