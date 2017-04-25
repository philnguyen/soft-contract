#lang racket

(define rx #rx"a regex")
(define px #px"a pregex")
(define brx #rx#"a byte-regex")
(define bpx #px#"a byte-pregex")

(define rx1 rx)
(define n 42)

(provide
 (contract-out
  [rx regexp?]
  [px pregexp?]
  [brx byte-regexp?]
  [bpx byte-pregexp?]
  [rx1 (not/c integer?)]
  [n (not/c regexp?)]))
