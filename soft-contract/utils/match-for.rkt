#lang typed/racket/base

(provide match-for match-for*)

(require racket/match)

(define-syntax-rule (match-for ([p e]) e* ...)
  (for ([x e]) (match-let ([p x]) e* ...)))

(define-syntax match-for*
  (syntax-rules ()
    [(_ ([p₁ e₁] [p e] ...) e* ...)
     (match-for ([p₁ e₁]) (match-for* ([p e] ...) e* ...))]
    [(_ () e* ...) (let () e* ...)]))
