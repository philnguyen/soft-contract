#lang racket

((contract (-> string? string?)
            (λ (x) (string-append x "!"))
            'pos
            'neg)
  5)
