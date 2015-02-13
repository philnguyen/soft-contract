Directory structure
==========================================

The system has two separate components for verification and generating counterexamples.
Directory [ce/](https://github.com/philnguyen/soft-contract/tree/pldi-aec-2015/soft-contract/ce)
is the main place that implements counterexample generation based on the work described in the paper.

* [examples/](https://github.com/philnguyen/soft-contract/tree/pldi-aec-2015/soft-contract/examples)
  contains example programs
* [benchmark-contract-overhead/](https://github.com/philnguyen/soft-contract/tree/pldi-aec-2015/soft-contract/benchmark-contract-overhead)
  contains simple benchmarks for contract overhead in 3 video games
* [benchmark-verification/](https://github.com/philnguyen/soft-contract/tree/pldi-aec-2015/soft-contract/benchmark-verification)
  contains tests for contract verification and counterexample generation
* [lang.rkt](https://github.com/philnguyen/soft-contract/blob/pldi-aec-2015/soft-contract/lang.rkt)
  defines the AST
* [read.rkt](https://github.com/philnguyen/soft-contract/blob/pldi-aec-2015/soft-contract/read.rkt)
  defines the parser
* [runtime.rkt](https://github.com/philnguyen/soft-contract/blob/pldi-aec-2015/soft-contract/runtime.rkt) defines closure, environment, and store
* [show.rkt](https://github.com/philnguyen/soft-contract/blob/pldi-aec-2015/soft-contract/show.rkt)
  defines pretty printing for debugging/final result
* [provability.rkt](https://github.com/philnguyen/soft-contract/blob/pldi-aec-2015/soft-contract/provability.rkt)
  defines the proof system
* [query-z3.rkt](https://github.com/philnguyen/soft-contract/blob/pldi-aec-2015/soft-contract/query-z3.rkt)
  defines the translation of runtime heaps, values, and contracts into `Z3`
* [query-cvc4.rkt](https://github.com/philnguyen/soft-contract/blob/pldi-aec-2015/soft-contract/query-cvc4.rkt)
  defines the translation of runtime heaps, values, and contracts into `CVC4`
* [verify/](https://github.com/philnguyen/soft-contract/blob/pldi-aec-2015/soft-contract/verify)
  defines infrastructure for verification
  - [delta.rkt](https://github.com/philnguyen/soft-contract/blob/pldi-aec-2015/soft-contract/verify/delta.rkt)
    defines primitives extended to abstract values
  - [machine.rkt]((https://github.com/philnguyen/soft-contract/blob/pldi-aec-2015/soft-contract/verify/machine.rkt)
    defines the CESK machine
* [ce/](https://github.com/philnguyen/soft-contract/blob/pldi-aec-2015/soft-contract/ce)
  defines infrastructure for counterexample generation
  - [delta.rkt](https://github.com/philnguyen/soft-contract/blob/pldi-aec-2015/soft-contract/ce/delta.rkt)
    defines primitives extended to abstract values (mostly duplicated, to be refactored)
  - [machine.rkt](https://github.com/philnguyen/soft-contract/blob/pldi-aec-2015/soft-contract/ce/machine.rkt)
    defines the CESK machine (mostly duplicated, to be refactored)
  - [model.rkt](https://github.com/philnguyen/soft-contract/blob/pldi-aec-2015/soft-contract/ce/model.rkt)
    defines instantiation of values
