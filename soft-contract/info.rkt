#lang info

(define collection "soft-contract")

(define pkg-desc "Contract verifier")

(define deps '("base"
               "bnf"
               "compiler-lib"
               "htdp-lib"
               "intern"
               "macro-debugger-text-lib"
               "math-lib"
               "profile-lib"
               "rackunit-typed"
               "set-extras"
               "typed-racket-hacks"
               "typed-racket-lib"
               "web-server-lib"
               "z3"
               "zo-lib"))

(define compile-omit-paths '("test"))

(define raco-commands
  '(("scv" soft-contract/cmdline "verify contracts" #f)))
