This is the scaled up version of SCV,
intended to be (eventually) usable for real Racket programs.

Installation
=========================================

### Install Z3 and Racket Z3 Library

This project depends on Z3 and Racket Z3 library. Installation instructions can be [are here](https://github.com/philnguyen/z3-rkt).

### Install the Verifier

Clone the repository:

> git clone git@github.com:philnguyen/soft-contract.git

> git checkout opt

Link:

> cd soft-contract/soft-contract

> raco link .

`cmdline.rkt` is the main file that runs the analysis.
Because type checking takes a while, you want to build it once first:

> raco make cmdline.rkt

To run the analysis on a file `example.rkt`, run:

> racket cmdline.rkt example.rkt

By default, the tool "havocs" all exported values from the module.
To just run the module from top to bottom without havoc-ing, use `-r`:

> racket cmdline.rkt -r test/programs/safe/sat.rkt
