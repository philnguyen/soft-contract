This is the scaled up version of SCV,
intended to be (eventually) usable for real Racket programs.

[![Build Status](https://travis-ci.org/philnguyen/soft-contract.png?branch=master)](https://travis-ci.org/philnguyen/soft-contract)

Installation
=========================================

### Install Z3 and set `$Z3_LIB`:

Install [Z3](https://github.com/Z3Prover/z3), then set `$Z3_LIB` to the **directory**
containing:
  - `libz3.dll` if you're on Windows
  - `libz3.so` if you're on Linux
  - `libz3.dylib` if you're on Mac


At this point, this only works with Z3 `4.4.1` and has been known not to work with later Z3 versions.
This will be fixed eventually.

### Install `soft-contract`

Clone the repository:

```
git clone git@github.com:philnguyen/soft-contract.git
```

Install:

```
cd soft-contract/soft-contract
raco pkg install
```

I will register this package on Racket Packages eventually.

Running
=========================================

First, insert the following line in each file.
(If you only verify 1 file, you may get away with not doing this)
```
(require soft-contract/fake-contract)
```

Use `raco scv` to run the analysis on one example at `test/programs/safe/octy/ex-14.rkt`:
```
raco scv test/programs/safe/octy/ex-14.rkt
```

If the program is big and you want to print out something that looks like progress,
use `-p`:
```
raco scv -p test/programs/safe/games/snake.rkt
```

To verify multiple files that depend on one another,
pass them all as arguments.
If you forget to include any file that's part of the dependency,
it'll error out asking you to include the right one.
```
raco scv -p test/programs/safe/multiple/*.rkt
```
