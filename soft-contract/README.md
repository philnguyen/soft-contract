This is the scaled up version of SCV,
intended to be (eventually) usable for real Racket programs.

How to use
=========================================

Clone the repository:

> git clone git@github.com:philnguyen/soft-contract.git

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

In order to be used with SCV, the file `example.rkt` should declare:

```{racket}
(require soft-contract/fake-contract)
```

And provide bindings as well as contracts *at the end* of the file:

```{racket}
(provide/contract
  [f (integer? . -> . integer?)])
```


(Experimental) New features
=========================================

### Primitives

Most functions in the Racket reference [section 4](http://docs.racket-lang.org/reference/data.html)
and some in [section 8](http://docs.racket-lang.org/reference/contracts.html)
are supported.


### Side effects

The tool no longer requires contracts to be pure.
It dynamically detects if the contract's result depends on a mutable state.
Results independent of mutable states are remembered
to eliminate any inconsistency later on.
(This is sound even if the contract modifies some state,
because no memoization is performed.)

For example, in the following, `weird-int?`'s side effect
doesn't prevent `f`'s range from verifying.

```{racket}
(define counter (box 0))

(define (weird-int? x)
  (set-box! counter (+ 1 (unbox counter)))
  (integer? x))

(: f : (→ weird-int?) → weird-int?)
(define (f g) (g))
```


### Inductive properties

SCV can (occasionally) verify inductive properties expressed in ordinary code.

```{racket}

(define (my-len xs)
  (cond [(cons? xs) (+ 1 (my-len (cdr xs)))]
        [else 0]))

(: my-map : [f : (any/c → any/c)] [xs : (listof any/c)]
            → (λ (ys) (= (my-len xs) (my-len ys))))
(define (my-map f xs)
  (cond [(cons? xs) (cons (car xs) (my-map f (cdr xs)))]
        [else null]))
```

The catch is this only works if it has the functions' source code available.
It doens't work for library functions.


#### TODOs/FIXMEs
* [ ] false pozes
* [ ] `case-lambda`
* [ ] all uses of functions with multiple ones (currently only pick 1, no keyword/vararg)
* [ ] `any` currently treated as `any/c`, which is wrong for multiple values
* [ ] mutable fields in user-defined structs (All facilities are there, with `box` a special instance. Just need to fix the parser.)
* [ ] index-out-of-bound currently blaming `Λ` instead of `vector-ref`'s user due to design flaw
* [ ] reasonable counterexamples, focusing on stateless ones.
      (Stateful one can trivially cheat with internal counter, then appropriate value for *ith* invocation,
       which is not that helpful to programmer).
* [ ] non-dependent contract is currently just special case of dependent.
      Range is re-evaluated at each application, which makes a difference if there are side effects.
