#lang racket

((contract (-> string? string?)
            (λ (x) (string-append x "!"))
            #f
            #f)
  "hi")
