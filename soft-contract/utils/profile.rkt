#lang typed/racket/base
(require typed/racket/unsafe)

(unsafe-require/typed profile
  [profile-thunk
   (∀ (X) ([(→ X)]
           [#:delay Nonnegative-Real
            #:repeat Natural
            #:use-errortrace? Any
            #:order (U 'topological 'self 'total)]
           . ->* . X))]
  [(profile-thunk profile-thunk2)
   (∀ (X Y) ([(→ (Values X Y))]
             [#:delay Nonnegative-Real
              #:repeat Natural
              #:use-errortrace? Any
              #:order (U 'topological 'self 'total)]
             . ->* . (Values X Y)))])

(unsafe-provide profile profile2 profile-thunk profile-thunk2)

(define-syntax-rule (profile e args ...)
  (profile-thunk (λ () e) args ...))

(define-syntax-rule (profile2 e args ...)
  (profile-thunk2 (λ () e) args ...))
