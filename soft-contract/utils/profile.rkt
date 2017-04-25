#lang typed/racket/base
(require/typed/provide profile
  [profile-thunk (∀ (X) ([(→ X)] [#:delay Nonnegative-Real #:repeat Natural #:use-errortrace? Any] . ->* . X))])
(provide profile)

(define-syntax-rule (profile e args ...)
  (profile-thunk (λ () e) args ...))
