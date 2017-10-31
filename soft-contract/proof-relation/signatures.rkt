#lang typed/racket/base

(provide (all-defined-out))

(require typed/racket/unit
         set-extras
         "../ast/signatures.rkt"
         "../runtime/signatures.rkt")

(define-signature local-prover^
  ([lift-p∋V : ((-σ -φ -h -V * → -R) → -σ -φ -h -V^ * → -R)]
   [p∋V : (-σ -φ -h -V * → -R)]
   [p∋V^ : (-σ -φ -h -V^ * → -R)]
   #;[p⇒p : (-h -h → -R)]
   #;[ps⇒p : ((℘ -h) -h → -R)]
   [sat-one-of : (-V^ (℘ Base) → -R)]
   [V-arity : (case->
               [-Clo → Arity]
               [-Case-Clo → Arity]
               [-V → (Option Arity)])]))

(define-signature external-prover^
  ([ext-prove : (-φ -h (Listof -V) → -R)]))
