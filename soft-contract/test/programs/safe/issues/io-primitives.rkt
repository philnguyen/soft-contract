#lang racket

(print "hi")
(print "hi" (current-output-port))
(print "hi" (current-output-port) 0)
(display (list 1 'sym))
(display (list 1 'sym #f) (current-output-port))
