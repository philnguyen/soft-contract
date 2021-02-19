#lang racket

(contract integer? 4 'me 'them)

(define n (+ 1 2 3))

(contract exact-positive-integer? (+ n n) 'me 'them)

(define str->sym string->symbol)

(define str->sym* (contract (string? . -> . symbol?) str->sym 'me 'them))

(define str->sym** (contract (string? . -> . symbol?) (λ (s) (string->symbol s)) 'me 'them))

(define str?->sym? (string? . -> . symbol?))

(define str->sym*** (contract str?->sym? (λ (s) (str->sym** s)) 'me 'them))

(provide
 (contract-out
  [str->sym*** str?->sym?]))
