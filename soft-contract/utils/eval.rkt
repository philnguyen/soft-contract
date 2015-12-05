#lang typed/racket/base

(provide within-time: @?)

;; evaluate an expression within given #seconds
;; return singleton list of value, or #f on timeout
(define-syntax-rule (within-time: τ n e ...)
  (let ([c : (Channelof (U #f (List τ))) (make-channel)])
    (define t₁ (thread (λ () (channel-put c (list (begin e ...))))))
    (define t₂ (thread (λ () (sleep n) (channel-put c #f))))
    (match (channel-get c)
      [#f  (kill-thread t₁) #f]
      [ans (kill-thread t₂) ans])))

;; Application with implicit #f for failure for expressions marked with (!)
;; e.g. (@? cons (! #f) 2) --> #f
;; e.g. (@? cons #f 2) --> ⟨1, 2⟩
(define-syntax @?
  (syntax-rules (!)
    [(_ f e ...) (@?* f (e ...) ())]))
(define-syntax @?*
  (syntax-rules (!)
    [(_ f ()             (x ...)) (f x ...)]
    [(_ f ((! e₁) e ...) (x ...))
     (let ([x₁ e₁])
       (if x₁ (@?* f (e ...) (x ... x₁)) #f))]
    [(_ f (e₁     e ...) (x ...))
     (let ([x₁ e₁])
       (@?* f (e ...) (x ... x₁)))]))
