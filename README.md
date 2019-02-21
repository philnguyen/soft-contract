[![Build Status](https://travis-ci.org/philnguyen/soft-contract.png?branch=pldi-19-ae)](https://travis-ci.org/philnguyen/soft-contract)

Artifact for "Soft Contract Verification for Higher-order Stateful Programs"
=============================================================

This repository contains the artifact for the research done in the paper
[*Soft-contract Verification for Higher-order Stateful Programs*](https://github.com/philnguyen/soft-contract/blob/popl18-ae/paper/main.pdf).

There are three components to this artifact:

* The contract verifier for Racket
* The set of benchmarks used in the paper
* The mechanization in Lean of soundness of symbolic execution
  in a minimal higher-order imperative language.
  
There are two options to evaluate the artifact:

* Option 1: by [obtaining the self-contained Virtualbox image](#option-1-obtain-the-self-contained-virtualbox-image)
* Option 2: by [cloning and building the repositories](#option-2-build-packages-from-source)

## Option 1: Obtain the self-contained Virtualbox image

The more convenient method for testing the artifact is to download and run
a virtual machine that contains the verifier, proof, and all their dependencies.

The image has been tested to work with Virtualbox `5.1.26`.
Instructions for
[downloading and installing Virtualbox](https://www.virtualbox.org/wiki/Downloads)
can be found on the official site.

1. Download the [OVA image](https://www.dropbox.com/s/86qkojng6zzvhhk/popl18-scv.ova?dl=0)
   (If you don't have a Dropbox account, no need to sign up: just dismiss the sign-up dialog.)

2. Launch the image:
   on most Linux or Windows desktops, double-clicking the file will do.
   Otherwise from Virtualbox, choose `File -> Import Appliance`.
   It is reccommended that you give the image at least `2048MB` of memory.
   
3. The image runs Lubuntu 16.04 64bit with log in information:

    * Username: `reviewer`
    * Password: `reviewer`
    
4. After the desktop loads, launch the terminal using the icon on the desktop.
    
5. To automate *all* the steps described in the next sections, execute:

        cd soft-contract
        make
        
An example of the expected output can be found at [log.txt](https://github.com/philnguyen/soft-contract/tree/popl18-ae/log.txt).

Below, we describe each step, along with the specific `make` target to just run that step.
We assume the working directory is `/home/reviewer/soft-contract`.
    
### Testing the implementation

#### Running the sanity test suite

The test suite contains many programs collected from other works
(and their incorrect variants that the tool should detect errors)
and bug reports. To just run the the test suite, run:

    make test

#### Reproducing benchmark tables from the paper

To run the benchmarks and generate tables listing positives
and verification time for each module,
type the following at the prompt:

    make tables
   
The tables should take around 1 hour to generate.

While the paper collapses several old benchmarks together
(e.g. `soft-typing`, `hors`, `occurence-typing`),
the script outputs each benchmark suite in details.
In addition, the number of checks have slightly fluctuated because
we changed the expansion of some language constructs.
In all cases, the estimated number of checks is always under-approximating.

Because the tool is still in development, some numbers have differed
since the paper's submission (some fewer positives, some faster programs,
some slower ones). We will update the paper's final version
to be consistent with the latest status.
   
#### Trying your own programs

To try the verifier on your own program, use command `raco scv` on a regular
Racket file:

    raco scv path/to/rkt/file
        
The verifier will output `safe` if the program is verified, or
report possible contract violation(s) with source locations.
   
You can start by modifying existing programs from the benchmarks above:

* [soft-contract/test/programs/safe/softy](https://github.com/philnguyen/soft-contract/tree/popl18-ae/soft-contract/test/programs/safe/softy):
  benchmarks collected from work on soft-typing.
* [soft-contract/test/programs/safe/octy](https://github.com/philnguyen/soft-contract/tree/popl18-ae/soft-contract/test/programs/safe/octy):
  benchmarks collected from work on occurence typing.
* [soft-contact/test/programs/safe/mochi](https://github.com/philnguyen/soft-contract/tree/popl18-ae/soft-contract/test/programs/safe/mochi):
  benchmarks collected from work on model-checking higher-order recursion schemes.
* [soft-contract/test/programs/safe/games](https://github.com/philnguyen/soft-contract/tree/popl18-ae/soft-contract/test/programs/safe/games):
  video games using extensive contracts.
* [soft-contract/test/programs/safe/real](https://github.com/philnguyen/soft-contract/tree/popl18-ae/soft-contract/test/programs/safe/real):
  larger, stateful programs collected from different sources.
     
Other benchmarks in the repository are either small program fragments
subsumed by mentioned benchmarks or programs with features not yet handled
by the current tool (e.g. control operators, optional keyword arguments,
gradually typed programs, etc.)
   
#### Browsing the implementation

An overview of the source code is as follow:

* [soft-contract/parse](https://github.com/philnguyen/soft-contract/tree/popl18-ae/soft-contract/parse):
  defines the parser that converts Racket syntax into an internal AST representation.
* [soft-contract/ast](https://github.com/philnguyen/soft-contract/tree/popl18-ae/soft-contract/ast):
  defines the internal representation of the AST.
  The [main AST definition](https://github.com/philnguyen/soft-contract/blob/popl18-ae/soft-contract/ast/signatures.rkt#L73)
  closely matches the documented
  [fully expanded program](https://docs.racket-lang.org/reference/syntax-model.html?q=fully%20expanded#%28part._fully-expanded%29).
* [soft-contract/runtime](https://github.com/philnguyen/soft-contract/tree/popl18-ae/soft-contract/runtime):
  defines internal runtime constructs for symbolic execution.
* [soft-contract/primitives](https://github.com/philnguyen/soft-contract/tree/popl18-ae/soft-contract/primitives):
  declares contracts (along with refinements) for primitives operations.
* [soft-contract/proof-relation](https://github.com/philnguyen/soft-contract/tree/popl18-ae/soft-contract/proof-relation):
  defines the proof relation between path-conditions, values, and first-order contracts.
* [soft-contract/reduction](https://github.com/philnguyen/soft-contract/tree/popl18-ae/soft-contract/reduction):
  defines the symbolic execution.
   
### Checking the proof

#### Checking the proof with Lean

To just check the proof, at the prompt, execute:

    make proof
    
The command should finish with no output if the proof goes through.
Otherwise, Lean will complain about some unproven theorem
(or those admited without proof using `sorry`).

#### Browsing the proof

The content of the proof script is as follow:

* [proof/definitions.lean](https://github.com/philnguyen/soft-contract/blob/popl18-ae/mechanized/definitions.lean): definition of lambda-calculus
  with integers, symbolic values, and mutable variables,
  along with run-time constructs.
* [proof/instantiation.lean](https://github.com/philnguyen/soft-contract/blob/popl18-ae/mechanized/instantiation.lean): definition of the approximation
  relation between different components.
* [proof/theorems.lean](https://github.com/philnguyen/soft-contract/blob/popl18-ae/mechanized/theorems.lean): proof of soundness of higher-order
  symbolic execution, with supporting lemmas proven in
  [proof/lemmas.lean](https://github.com/philnguyen/soft-contract/blob/popl18-ae/mechanized/lemmas.lean) and
  [proof/helper_lemmas.lean](https://github.com/philnguyen/soft-contract/blob/popl18-ae/mechanized/helper_lemmas.lean).
  

## Option 2: Build packages from source

The more involved way to test the artifact is to clone and build `soft-contract`
and Lean yourself.

### Building and installing `soft-contract`

1. Download [Racket 6.10](https://download.racket-lang.org/).
   This project is known to *not* work with previous releases of Racket.

2. Download and install [Z3](https://github.com/Z3Prover/z3/releases).
   This project has been tested to work with Z3 `4.5.0`.
   
3. Set the environment variable `$Z3_LIB` to `libz3.dll`, `libz3.so`,
   or `libz3.dylib`, depending on your system being Windows, Linux, or Mac,
   respectively.
   
4. In the rare case that you have a previous version of `soft-contract`
   installed, remove it first:
   
        raco pkg remove soft-contract
        
5. Clone and build the `soft-contract` repository:

        git clone git@github.com:philnguyen/soft-contract.git
        cd soft-contract/soft-contract
        git checkout popl18-ae
        raco pkg install --deps search-auto
        
6. Information for generating the tables, verifying your own programs,
   and browsing the source code is the same as in the
   [previous section](#testing-the-implementation).
        

### Building `Lean` and checking the proof

1. Download Lean commit
   [`a9821f6437`](https://github.com/leanprover/lean/archive/a9821f643735de59efaf6eeabd0bfa8e9ae914fe.zip).
   Because Lean is in rapid development, our proof script is not compatible
   with recent releases.
   (Language-wise, our script is compatible with Lean 3.0.0,
   but the release seg-faults on the script,
   which the Lean authors quickly fixed in this commit.)
   
2. Instructions for building Lean on different systems can be found on Lean's
   [Github page](https://github.com/leanprover/lean#build-instructions).
   
3. Information for running the proof script and browsing the proof
   is the same as in the [previous section](#checking-the-proof).
