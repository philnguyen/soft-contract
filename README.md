Artifact for "Relatively Complete Counterexamples for Higher-order Programs"
============================================================================

[![Build Status](https://travis-ci.org/philnguyen/soft-contract.png?branch=pldi-aec-2015)](https://travis-ci.org/philnguyen/soft-contract)

This repository contains the source code and benchmarks used to evaluate
the research done in *Relatively Complete Counterexamples for Higher-order Programs*
[accepted to PLDI 2015](https://github.com/philnguyen/soft-contract/blob/pldi-aec-2015/paper/pldi15-paper103.pdf).

We evaluate our method on programs written in an untyped functional language
representing [Core Racket](#supported-language)
and demonstrate its effectiveness against various common programing idioms.
The benchmarks are collected from different verification techniques on typed and untyped languages,
where benchmarks originally written in typed languages
are translated to untyped programs with contracts.
The tool itself is written in [Racket](http://racket-lang.org/).

There are three options to evaluate the artifact:

* By [the online evaluator](#try-the-online-evaluator)
* By [the self-contained Virtualbox image](#obtain-the-self-contained-virtualbox-image)
* By [cloning and building the repositories](#build-from-source-code)

## Try the online evaluator

The quickest and most convenient way to test the artifact
is to use the [online evaluator](http://scv.umiacs.umd.edu/) hosted
at the University of Maryland, which provides a REPL for SCV Racket.
All of the benchmarks and examples are available to try or
you experiment with your own programs.

No indentifying information is retained in the server logs, 
although we do record the programs entered
into the REPL for use as verification benchmarks.

We recommend using `Google Chrome`, even though the website is also usable in `Firefox`
(with a different layout).

## Obtain the self-contained Virtualbox image

The next most convenient method for testing the artifact is to download and run
a virtual machine that contains SCV Racket and all of its dependencies.

The image has been tested to work with Virtualbox `4.3.18`.
Instructions for [downloading and installing Virtualbox](https://www.virtualbox.org/wiki/Downloads)
can be found on the official site.

1. Download the [Virtualbox image](https://drive.google.com/file/d/0B5Xtjx9YdmWxMkNKUUo2cVVlbEU/view?usp=sharing) 
(~3.4 GB; hosted on Google Drive),
which contains built source code for `soft-contract`, the `try-scv-racket` web server, and benchmarks.

2. Launch Virtualbox:

  * Click `New`
  * Enter name and operating system:
    - Name: *(any name)*
	- Type: `Linux`
	- Version: `Ubuntu (32 bit)`
  * Next, set `Memory size`, recommended at least `1024MB`
  * Next, select `Use an existing virtual drive file`, then point to the downloaded disk image, then press `Create`
  * With the newly created machine selected, press `start`

2. The image runs Lubuntu 14.10 32 bit. When the desktop loads, log in:

  * Username: `aec`
  * Password: `aec`

3. There are desktop icons for the terminal and browser.

  Directory structure:

  * `/home/aec/soft-contract`: source code for Soft Contract Verification with counterexamples
  * `/home/aec/soft-contract/benchmark-verification`: benchmarks categorized into safe and unsafe programs
  * `/home/aec/try-scv-racket`: the webserver for interactive testing

4. To run the benchmarks, open the terminal:

        cd /home/aec/soft-contract/benchmark-verfication
        raco test main.rkt

5. To run the server and try out the web tool at [http://localhost:8080](http://localhost:8080).


        cd /home/aec/try-scv-racket
        racket main.rkt

   `Google Chrome`'s homepage is set to [http://localhost:8080](http://localhost:8080).

## Build from source code

The final and most involved way to test the artifact is to download
and build the system yourself.

### Build the `soft-contract` repository

1. Obtain and install [Racket snapshot](http://www.cs.utah.edu/plt/snapshots/).

2. Obtain and install [Z3](http://z3.codeplex.com/)

3. Clone and build the repository

        git clone https://github.com/philnguyen/soft-contract.git
	    cd path/to/soft-contract
    	raco make main.rkt
	    raco link

4. Run the benchmarks. This step assumes `z3` is available in `$PATH`.

        cd path/to/soft-contract/benchmark-verification
	    raco test main.rkt

### Build the `try-scv-racket` server

This step assumes that you have built `soft-contract`
and performed `raco link` as in the [previous section](#Build the `soft-contract` repository)

1. Clone the `try-scv-racket` repository

        git clone https://github.com/plum-umd/try-scv-racket.git

2. Launch the server at [http://localhost:8080](http://localhost:8080)

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
