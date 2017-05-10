#lang racket

(provide
 ;; String 
 EOM
 DONE
 
 ;; constants, regexps that match PATH, DISABLE, and ENABLE requests
 PATH 
 DISABLE
 ENABLE
 
 ;; InputPort OutputPort -> Void 
 ;; read FROM, DISABLE, and ENABLE requests input-port, write responses to output-port, loop
 run-t)

;; ===================================================================================================

(require "t-view.rkt")

(define PATH    #rx"from (.*) to (.*)$")
(define DISABLE #rx"disable (.*)$")
(define ENABLE  #rx"enable (.*)$")

(define DONE    "done")
(define EOM     "eom")

(define manage (new manage%))

(define (run-t next)
    (cond
      [(regexp-match PATH next)
       => (lambda (x)
       (define x2 (second x))
       (define x3 (third x))
       (unless (and x2 x3) (error 'run-t "invariat error"))
       (send manage find x2 x3))]
      [(regexp-match DISABLE next)
       => (lambda (x)
       (define x2 (second x))
       (unless x2 (error 'run-t "invariants"))
       (status-check add-to-disabled x2))]
      [(regexp-match ENABLE next)
       => (lambda (x)
       (define x2 (second x))
       (unless x2 (error 'run-t "invariants"))
       (status-check remove-from-disabled x2))]
      [else "message not understood"]))

(define-syntax-rule
  (status-check remove-from-disabled enabled)
  (let ([status (send manage remove-from-disabled enabled)])
    (if (boolean? status)
        DONE
        status)))

