soft-contract
=============

[![Build Status](https://travis-ci.org/philnguyen/soft-contract.png?branch=master)](https://travis-ci.org/philnguyen/soft-contract)

Installation
------------------------

To install, clone the `racket` branch of this repository, then:

	cd path/to/soft-contract
    raco pkg install


Examples and Usage
------------------------

This collection implements a small functional language with contract verification
and counterexample generation.
Examples are under [examples/](https://github.com/philnguyen/soft-contract/tree/release/examples)

You need to have [Z3](http://z3.codeplex.com/releases) available in your path.
This program has been tested to work with Z3 `4.3.2`.

The demo currently supports the following subset of Racket:

    program          ::= sub-module-form … | sub-module-form … (require id …) expr
	sub-module-form  ::= (module module-id racket
	                       (provide provide-spec …)
                           (require require-spec …)
						   (struct id (id …)) …
                           (define id value) …)
    provide-spec     ::= id | (contract-out p/c-item …)
    p/c-item         ::= (id contract) | (struct id ([id contract] …))
	require-spec     ::= (submod ".." module-id)
	value            ::= (lambda (id …) expr) | number | boolean | string | symbol | op
	expr             ::= id | (if expr expr expr) | (expr expr …)
	contract         ::= expr | any/c | (or/c contract …) | (and/c contract …)
	                   | (list/c contract) | (listof contract)
	                   | (->i ([id contract] …₁) (res (id …₁) contract))
    op               ::= + | - | * | / | string-length
	                   | number? | real? | integer? | boolean? | false? | cons? | empty?
