Directory structure
==========================================

The system has two separate components for verification and generating counterexamples.

* `examples` contains example programs
* `benchmark-contract-overhead` contains simple benchmarks for contract overhead in 3 video games
* `benchmark-verification` contains tests for contract verification and counterexample generation
* `lang.rkt` defines the AST
* `read.rkt` defines the parser
* `runtime.rkt` defines closure, environment, and store
* `show.rkt` defines pretty printing for debugging/final result
* `provability.rkt` defines the proof system
* `query-z3.rkt` defines the translation of runtime heaps, values, and contracts into `Z3`
* `query-cvc4.rkt` defines the translation of runtime heaps, values, and contracts into `CVC4`
* `verify` defines infrastructure for verification
  - `delta.rkt` defines primitives extended to abstract values
  - `machine.rkt` defines the CESK machine
* `ce` defines infrastructure for counterexample generation
  - `delta.rkt` defines primitives extended to abstract values (mostly duplicated, to be refactored)
  - `machine.rkt` defines the CESK machine (mostly duplicated, to be refactored)
  - `model.rkt` defines instantiation of values
