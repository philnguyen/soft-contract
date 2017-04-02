This is the scaled up version of SCV,
intended to be (eventually) usable for real Racket programs.

[![Build Status](https://travis-ci.org/philnguyen/soft-contract.png?branch=opt)](https://travis-ci.org/philnguyen/soft-contract)

Installation
=========================================

### Install Z3 and Racket Z3 Library

This project depends on Z3 and Racket Z3 library. Installation instructions [are here](https://github.com/philnguyen/z3-rkt).

### Install the Verifier

Clone the repository:

> git clone git@github.com:philnguyen/soft-contract.git

Link:

> cd soft-contract/soft-contract

> raco link .

`cmdline.rkt` is the main file that runs the analysis.
Because type checking takes a while, you want to build it once first:

> raco make -j $(nproc) cmdline.rkt


Running
=========================================

To run the analysis on one example at `test/programs/safe/octy/ex-14.rkt`, run:

> racket cmdline.rkt test/programs/safe/octy/ex-14.rkt

If the program is big and you want to print out something that looks like progress,
use `-p`:

> racket cmdline.rkt -p test/programs/safe/games/snake.rkt
