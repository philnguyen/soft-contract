#lang typed/racket/base

(provide with-time-limit)

(require syntax/parse/define
         (for-syntax racket/base))

;; evaluate an expression within given #seconds
;; return singleton list of value, or #f on timeout
(define-syntax-parser with-time-limit
  [(_ (~literal :) τ n e ...)
   #'(let ([c : (Channelof (U #f (List τ))) (make-channel)])
       (define t₁ (thread (λ () (with-handlers ([exn? (λ (_) (channel-put c #f))])
                                  (channel-put c (list (let () e ...)))))))
       (define t₂ (thread (λ () (sleep n) (channel-put c #f))))
       (define (kill-all) (kill-thread t₁) (kill-thread t₂))
       (cond
         [(channel-get c) => (λ ([ans : (List τ)]) (kill-all) ans)]
         [else (kill-all) #f]))]
  [(_ n e ...)
   #'(with-time-limit : Any n e ...)])
