[![Build Status](https://travis-ci.org/philnguyen/soft-contract.png?branch=dev-adi)](https://travis-ci.org/philnguyen/soft-contract)

Soft Contract Verifier
=============================================================

This is a branch of the tool that's under active development, with the main
differences:
* Writing the analysis as (a variant of) [abstract definitional interpreter]
(https://dl.acm.org/doi/pdf/10.1145/3110256?download=true) with an improved
cache-fixing loop that reduces redundant computation.
* Per-step abstract garbage collection with respect to a much smaller
live set, thanks to stack irrelevance and big-step formulation,
as well-described in
[Stack-Liberated Abstract Garbage Collection](https://icfp19.sigplan.org/details/scheme-2019-papers/12/Stack-Liberated-Abstract-Garbage-Collection),
although the technique was independently discovered.
* Dropping dependence on Z3 in favor of an internal solver,
as the analysis's typical use case is a large number of very simple queries.

The tool is expected to be plagued with bugs and not ready for production.

The previous versions of the implementation are archived in branches
[icfp14](https://github.com/philnguyen/soft-contract/tree/icfp14),
[pldi-aec-2015](https://github.com/philnguyen/soft-contract/tree/pldi-aec-2015),
[jpf](https://github.com/philnguyen/soft-contract/tree/jfp),
[popl18-ae](https://github.com/philnguyen/soft-contract/tree/popl18-ae).

## Installation

Clone this repository

    git clone https://github.com/philnguyen/soft-contract.git

Navigate into the inner `soft-contract` directory and install using `raco`:

    cd soft-contract/soft-contract
    raco pkg install --deps search-auto

## Usage

To verify one or more modules, use `raco scv` command:

    raco scv paths/to/files.rkt ...

### Non-standard construct

Using non-standard constructs require `fake-contract`:

    (require soft-contract/fake-contract)
