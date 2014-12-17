soft-contract
=============

Installation
------------------------

    raco pkg install soft-contract


Examples and Usage
------------------------

This collection implements a small functional language with contract verification
and counterexample generation.
Examples are under [examples/](https://github.com/philnguyen/soft-contract/tree/release/examples)

You need to have [Z3](http://z3.codeplex.com/releases) available in your path.
This program has been tested to work with Z3 `4.3.2`.

The demo currently supports the following subset of Racket:

    program          ::= module-form
	sub-module-form  ::= (module module-name racket
	                       (provide provide-spec …)
                           (require require-spec …)
                           (define name value) …)
    provide-spec     ::= (name contract)
	require-spec     ::= (submod ".." module-name)
	value            ::= (λ (var) expr) | number | boolean | string | symbol | op
	expr             ::= var | (if expr expr expr) | (expr expr …)
	contract         ::= expr | (or/c contract …) | (and/c contract …)
	                   | (->i ([var contract] …) (res (var …) contract))
    op               ::= + | - | * | / | string-length
	                   | number? | real? | integer? | boolean? | false? | cons? | empty?
