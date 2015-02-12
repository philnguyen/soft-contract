Artifact for "Relatively Complete Counterexamples for Higher-order Programs"
============================================================================

[![Build Status](https://travis-ci.org/philnguyen/soft-contract.png?branch=pldi-aec-2015)](https://travis-ci.org/philnguyen/soft-contract)

This repository contains the source code and benchmarks used to evaluate
the research done in *Relatively Complete Counterexamples for Higher-order Programs*
[submitted to PLDI 2015](https://github.com/philnguyen/soft-contract/blob/pldi-aec-2015/paper/pldi15-paper103.pdf).

We evaluate our method on programs written in an untyped functional language
representing [Core Racket](#supported-language)
and demonstrate its effectiveness against various common programing idioms.
The benchmarks are collected from different verification techniques on typed and untyped languages,
where benchmarks originally written in typed languages
are translated to untyped programs with contracts.
The tool itself is written in [Racket](http://racket-lang.org/).

There are three ways to evaluate the artifact:

* By [the self-contained Virtualbox image](#obtain-the-self-contained-virtualbox-image)
* By [the online evaluator](#try-the-online-evaluator)
* By [building `soft-contract` repository](#build-from-source-code)

## Obtain the self-contained Virtualbox image

1. Download the [Virtualbox image](https://drive.google.com/file/d/0B5Xtjx9YdmWxVlh2dWo5WG40czA/view?usp=sharing)
containing source code for `SCV`, the `try-scv-racket` webserver, and benchmarks.

2. The image runs Lubuntu 14.10 32 bit. When the desktop loads, log in:

  * Username: `aec`
  * Password: `aec`

3. Press `Ctrl + Alt + t` to launch the terminal.

  Directory structure:

  * `/home/aec/soft-contract`: source code for Soft Contract Verification with counterexamples
  * `/home/aec/soft-contract/benchmark-verification`: benchmarks categorized into safe and unsafe programs
  * `/home/aec/try-scv-racket`: the webserver for interactive testing

4. To run the benchmarks

    cd /home/aec/soft-contract/benchmark-verfications
    raco test main.rkt

5. To run the server and try out the web tool at [http://localhost:8080]

    cd /home/aec/try-scv-racket
    racket main.rkt


## Try the online evaluator

The quickest way to try out the tool is through the [online evaluator](http://scv.umiacs.umd.edu/)
with many examples.

## Build from source code

### Build the `soft-contract` repository

1. Obtain [Racket snapshot](http://www.cs.utah.edu/plt/snapshots/).

2. Obtain [Z3](http://z3.codeplex.com/)

3. Clone and build the repository

    git clone https://github.com/philnguyen/soft-contract.git
	cd path/to/soft-contract
	raco make main.rkt
	raco link

4. Run the benchmarks

    cd path/to/soft-contract/benchmark-verification
	raco test main.rkt

### Build the `try-scv-racket` server

This step assumes that you have built `soft-contract`
and performed `raco link` as in the [previous section](#Build the `soft-contract` repository)

1. Clone the `try-scv-racket` repository

    git clone https://github.com/plum-umd/try-scv-racket.git

2. Launch the server at [http://localhost:8080]

    cd path/to/try-scv-racket
	racket main.rkt
	

## Supported Language

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
