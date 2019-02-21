Artifact for "Soft Contract Verification for Higher-order Stateful Programs"
=============================================================

This repository contains the static checker for the research done in the paper
[*Size-change Termination as a Contract*](https://github.com/philnguyen/termination/blob/pldi-19-ae/paper/main.pdf).

The main instructions are in the [`termination` repository](https://github.com/philnguyen/termination/tree/pldi-19-ae),
which subsumes the instructions below for just building the static checker.

* Prerequisite: install Z3:

    + Download and install [Z3](https://github.com/Z3Prover/z3/releases).
    This project has been tested to work with Z3 `4.5.0`.
    + Set the environment variable `Z3_LIB` to the directory containing
     `libz3.dll`, `libz3.so`, or `libz3.dylib`, depending on the system being
     Windows, Linux, or Mac, respectively.

* Installing `soft-contract` package:

    + In the rare case that you have a previous version of `soft-contract` installed, remove it first:
    
            raco pkg remove soft-contract
            
    + Clone and build the `soft-contract` repository:
    
            git clone https://github.com/philnguyen/soft-contract.git
            cd soft-contract/soft-contract
            git checkout pldi-19-ae
            raco pkg install --deps search-auto

To automate all the tests, under `soft-contract/soft-contract`, run:

    make test
