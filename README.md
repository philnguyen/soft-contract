Higher-order Contract Verification with Counterexamples
=============

[![Build Status](https://travis-ci.org/philnguyen/soft-contract.png?branch=pldi-aec-2015)](https://travis-ci.org/philnguyen/soft-contract)


### Obtain the self-contained Virtualbox image

You can download the [Virtualbox image](https://drive.google.com/file/d/0B5Xtjx9YdmWxVlh2dWo5WG40czA/view?usp=sharing)
containing source code for `SCV`, the `try-scv-racket` webserver, and benchmarks.

The image runs Lubuntu 14.10 32 bit.


* Username: `aec`
* Password: `aec`

When the desktop loads, press `Ctrl + Alt + t` to launch the terminal.

Directory structure:

* `/home/aec/soft-contract`: source code for Soft Contract Verification with counterexamples
* `/home/aec/soft-contract/benchmark-verification`: benchmarks categorized into safe and unsafe programs
* `/home/aec/try-scv-racket`: the webserver for interactive testing

### Run the benchmarks

    cd /home/aec/soft-contract/benchmark-verfications
    raco test main.rkt

### Run the server

    cd /home/aec/try-scv-racket
    racket main.rkt

Then open the link at `http://localhost:8080` to try out the web tool.
There are examples to start with.

### Supported Language

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
