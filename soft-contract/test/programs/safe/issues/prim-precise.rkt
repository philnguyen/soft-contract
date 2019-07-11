#lang racket/base

(if (= (+ 2 3) 5) 'ok (/ 1 0))
(if (not (= (+ 2 2) 5)) 'ok (/ 1 0))
