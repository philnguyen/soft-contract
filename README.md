Artifact for "Soft-contract Verification for Higher-order Stateful Programs"
=============================================================

This repository contains the artifact for the research done in the paper
[*Soft-contract Verification for Higher-order Stateful Programs*](https://github.com/philnguyen/soft-contract/blob/dev/paper/main.pdf).

There are three components to this artifact:

* The contract verifier for Racket
* The set of benchmarks used in the paper
* The mechanization in Lean of soundness of symbolic execution
  in a minimal higher-order imperative language.
  
There are two options to evaluate the artifact.

* By [obtaining the self-contained Virtualbox image](#option-1-obtain-the-self-contained-virtualbox-image)
* By [cloning and building the repositories](#option-2-build-packages-from-source)

## Option 1: Obtain the self-contained Virtualbox image

The more convenient method for testing the artifact is to download and run
a virtual machine that contains the verifier, proof, and all their dependencies.

The image has been tested to work with Virtualbox `5.1.26`.
Instructions for
[downloading and installing Virtualbox](https://www.virtualbox.org/wiki/Downloads)
can be found on the official site.

1. Download the [OVA image](FIXME link)

2. Launch the image:
   on most Linux or Windows desktops, double-clicking the file will do.
   Otherwise from Virtualbox, choose `File -> Import Appliance`.
   It is reccommended that you give the image at least `2048MB` of memory.
   
3. The image runs Lubuntu 16.04 64bit with log in information:

    * Username: `reviewer`
    * Password: `reviewer`
    
### Testing the implementation

1. To run the benchmarks and generate tables listing positives
   and verification time for each module,
   type the following at the prompt:

        raco popl18-gen-table
        
   An example of the expected output can be found at [log.txt](FIXME link).
   
2. To try the verifier on your own program, use command `raco scv` on a regular
   Racket file:

        raco scv path/to/rkt/file
        
   The verifier will output `safe` if the program is verified, or
   reports possible violation with some contracts with source locations.
   
   You can start by modifying existing programs used in the benchmarks above:

   * [soft-contract/test/programs/safe/softy](https://github.com/philnguyen/soft-contract/tree/dev/soft-contract/test/programs/safe/softy):
     benchmarks collected from work on soft-typing.
   * [soft-contract/test/programs/safe/octy](https://github.com/philnguyen/soft-contract/tree/dev/soft-contract/test/programs/safe/octy):
     benchmarks collected from work on occurence typing.
   * [soft-contact/test/programs/safe/mochi](https://github.com/philnguyen/soft-contract/tree/dev/soft-contract/test/programs/safe/mochi):
     benchmarks collected from work on model-checking higher-order recursion schemes.
   * [soft-contract/test/programs/safe/games](https://github.com/philnguyen/soft-contract/tree/dev/soft-contract/test/programs/safe/games):
     video games using extensive contracts.
   * [soft-contract/test/programs/safe/real](https://github.com/philnguyen/soft-contract/tree/dev/soft-contract/test/programs/safe/real):
     larger, stateful programs collected from different sources.
   
3. An overview of the source code:

   * [soft-contract/parse](https://github.com/philnguyen/soft-contract/tree/dev/soft-contract/parse):
     defines the parser that converts Racket syntax into an internal AST representation.
   * [soft-contract/ast](https://github.com/philnguyen/soft-contract/tree/dev/soft-contract/ast):
     defines the internal representation of the AST.
     The [main AST definition](https://github.com/philnguyen/soft-contract/blob/dev/soft-contract/ast/signatures.rkt#L73)
     closely matches the documented
     [fully expanded program](https://docs.racket-lang.org/reference/syntax-model.html?q=fully%20expanded#%28part._fully-expanded%29).
   * [soft-contract/runtime](https://github.com/philnguyen/soft-contract/tree/dev/soft-contract/runtime):
     defines internal runtime constructs for symbolic execution.
   * [soft-contract/primitives](https://github.com/philnguyen/soft-contract/tree/dev/soft-contract/primitives):
     declares contracts (along with refinements) for primitives operations.
   * [soft-contract/proof-relation](https://github.com/philnguyen/soft-contract/tree/popl-18/soft-contract/proof-relation):
     defines the proof relation between path-conditions, values, and first-order contracts.
   * [soft-contract/reduction](https://github.com/philnguyen/soft-contract/tree/popl-18/soft-contract/reduction):
     defines the symbolic execution.
   
### Checking the proof

To run all the proof, at the prompt, execute:

    lean proof/*.lean
    
The command should finish with no output if the proof goes through.
Otherwise, Lean will complain with some unproven theorem.

The content of the proof script is as follow:

* [proof/definitions.lean](https://github.com/philnguyen/soft-contract/blob/dev/mechanized/definitions.lean): definition of lambda-calculus
  with integers, symbolic values, and mutable variables,
  along with run-time constructs.
      
* [proof/instantiaions.lean](https://github.com/philnguyen/soft-contract/blob/dev/mechanized/instantiations.lean): definition of the approximation
  relation between different components.
  
* [proof/theorems.lean](https://github.com/philnguyen/soft-contract/blob/dev/mechanized/theorems.lean): proof of soundness of higher-order
  symbolic execution, with supporting lemmas proven in
  [proof/lemmas.lean](https://github.com/philnguyen/soft-contract/blob/dev/mechanized/lemmas.lean) and
  [proof/helper_lemmas.lean](https://github.com/philnguyen/soft-contract/blob/dev/mechanized/helper_lemmas.lean).
  

## Option 2: Build packages from source

### Building and installing `soft-contract`

1. Download [Racket 6.10](https://download.racket-lang.org/).
   This project is known to *not* work with previous releases of Racket.

2. Download and install [Z3](https://github.com/Z3Prover/z3/releases).
   This project has been tested to work with Z3 `4.5.0` and `4.4.1`.
   
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
        raco pkg install
        
6. Information for generating the tables, verifying your own programs,
   and browsing the source code is the same as in the
   [previous section](#testing-the-implementation).
        

### Building `Lean` and checking the proof

1. Download Lean commit
   [`a9821f6437`](https://github.com/leanprover/lean/archive/a9821f643735de59efaf6eeabd0bfa8e9ae914fe.zip).
   Because Lean is in rapid development, our proof script is not compatible
   with recent releases.
   
2. Instructions for building Lean on different systems can be found on their
   [Github page](https://github.com/leanprover/lean#build-instructions).
   
3. Information for running the proof script and browsing the proof
   is the same as in the [previous section](#checking-the-proof).
