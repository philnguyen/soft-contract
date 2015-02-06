#lang scribble/manual
@(require scriblib/figure)

@title{Higher-order Contract Verification with Counterexamples}


@section{Usage}

@subsection{Run the benchmarks}
In directory @tt{/home/aec/soft-contract/benchmark-verification}, run:

@codeblock|{
raco test main.rkt
}|

This will run the test suite, reporting the time it takes for each program
and printing out the counterexamples for unsafe programs.

@subsection{Run the web server}
In directory @tt{/home/aec/try-racket-scv}, run:

@codeblock|{
racket main.rkt
}|

This will start the web server, which you can interact with at @url{http://localhost:8080}.
The webpage gives some example programs to start with, including those in the testsuite.

You can also enter your own program to verify.
We support the following subset of Racket:

@figure["Syntax" "Syntax"]{
@racketgrammar*[#:literals (module racket provide provide/contract define submod lambda
                             if cond else -> + - * / string-length number? real?
                             integer? boolean? false? cons? empty?
                             and/c or/c ->i list/c listof
                             =/c >/c >=/c </c <=/c)
                [program (sub-module-form ...)
                         (sub-module-form ... (require id ...) expr)]
                [sub-module-form (module module-name racket
                                   (provide provide-spec ...)
                                   (require require-spec ...)
                                   (struct id (id ...))
                                   (define id value) ...)]
                [provide-spec id (contract-out p/c-item ...)]
                [p/c-item (id contract) (struct id ([id contract] ...))]
                [require-spec (submod ".." module-id)]
                [value (lambda (id ...) expr) number boolean string symbol op]
                [expr id (if expr expr expr) (expr expr ...)
                      (cond [expr expr] ... [else expr])]
                [contract expr (or/c contract ...) (and/c contract ...)
                          (list/c contract) (listof contract)
                          (=/c expr) (>/c expr) (>=/c expr) (</c expr) (<=/c expr)
                          (->i ([id contract] ..._1)
                               (res (id ..._1) contract))]
                [op + - * / string-length
                    number? real? integer? boolean? false? cons? empty?]]}

