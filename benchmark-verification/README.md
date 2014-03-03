To run the benchmarks, you need to have [Racket](http://racket-lang.org/) and [CVC4 1.3 and up](http://cvc4.cs.nyu.edu/web/) installed. This program assumes "cvc4" is available in your system's path. There should be no other prerequisites to run the program.

The program has been tested to work with Racket 5.3.5 and 6.0 and CVC4 1.3.

Each benchmark times out after 20 minutes.
To run all tests and print out results, run:
> racket run.rkt

There will be a long initial delay.

In pretty-printed results, elipses `...` stand for free variables,
and `L₁`, `L₂`, etc. stand for a labels.

To run only specific tests, for example, only `foldr` and `foldl`, run:
> racket run.rkt foldl.sch foldr.sch

Changes since submission to ICFP on March 1st:
* `cpstak` no longer timeouts
