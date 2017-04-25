#lang scribble/manual
@(require scriblib/figure)

@title{Soft Contract Verification}


@section{Installation}

@codeblock|{
raco pkg install soft-contract
}|


@section{Usage}

This collection implements a small functional language with contract verification
and counterexample generation.

You need to have Z3 in your path.
This program has been tested to work with Z3 4.3.2.

The demo currently supports the following subset of Racket:

@figure["Syntax" "Syntax"]{
@racketgrammar*[#:literals (module racket provide/contract define submod lambda
                             if cond else -> + - * / string-length number? real?
                             integer? boolean? false? cons? empty?
                             and/c or/c ->i)
                [program sub-module-form]
                [sub-module-form (module module-name racket
                                   (provide/contract provide-spec ...)
                                   (define id value) ...)]
                [provide-spec (id contract)]
                [require-spec (submod ".." module-name)]
                [value (lambda (id) expr) number boolean string symbol empty op]
                [expr id (if expr expr expr) (expr expr ...)
                      (cond [expr expr] ... [else expr])]
                [contract expr (or/c contract ...) (and/c contract ...)
                          (->i ([id contract] ...)
                               (id (id ...) contract))]
                [op + - * / string-length
                    number? real? integer? boolean? false? cons? empty?]]}


@section{Examples}

Example programs can be found under @bold{examples/}

