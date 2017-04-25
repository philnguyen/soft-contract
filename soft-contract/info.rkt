#lang info

(define collection "soft-contract")

(define pkg-desc "Contract verifier")

(define deps '("base"
               "typed-racket-lib"
               "typed-racket-more"
               "z3"
               "bnf"
               "intern"
               "set-extras"))

(define compile-omit-paths '("test"))

(define raco-commands
  '(("scv" soft-contract/cmdline "verify contracts" #f)))
