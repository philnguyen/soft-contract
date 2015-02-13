Overview of benchmarks
========================

We categorized programs into safe and unsafe.
Ideally, we should verify all safe programs
(in [`safe`](https://github.com/philnguyen/soft-contract/blob/pldi-aec-2015/soft-contract/benchmark-verification/safe))
and generate counterexamples for all unsafe ones
(in [`fail-ce`](https://github.com/philnguyen/soft-contract/blob/pldi-aec-2015/soft-contract/benchmark-verification/fail-ce)).
Unfortunately, verification is neccesarily incomplete in practice.
We therefore have to weaker categories
 * [`fail`](https://github.com/philnguyen/soft-contract/blob/pldi-aec-2015/soft-contract/benchmark-verification/fail):
   the verification should at least recognize that the program is potentially buggy
even if it cannot generate a counterexample (due to limitation of the underlying solver, for example)
 * [`no-ce`](https://github.com/philnguyen/soft-contract/blob/pldi-aec-2015/soft-contract/benchmark-verification/no-ce):
   the verification may fail to verify the correct program, reporting a *probable* contract violation, but under no circumstance should it produce a counterexample. This category is currently empty.

Overtime, we move tests from `fail` and `no-ce` to the stronger categories `fail-ce` and `safe`, respectively, and use integration testing to prevent regression in precision.
