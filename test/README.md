Test directories:

* `safe`: *Safe* programs we expect the tool to *verify*
* `fail-ce`: *Wrong* programs we expect the tool to generate a real *counterexample*
* `fail`: *Wrong* programs where it's ok for the tool not to generate a counterexample
* `no-ce`: *Safe* programs the tool may fail to verify, but must *not generate any bogus counterexample*

So `safe` and `fail-ce` are ideal cases. The other two are weaker.
