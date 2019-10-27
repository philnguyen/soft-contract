[![Build Status](https://travis-ci.org/philnguyen/soft-contract.png?branch=dev-adi)](https://travis-ci.org/philnguyen/soft-contract)

Soft Contract Verifier
=============================================================

## Installation

Clone this repository

    git clone https://github.com/philnguyen/soft-contract.git

Navigate into the inner `soft-contract` directory and install using `raco`:

    cd soft-contract/soft-contract
    raco pkg install --deps search-auto

## Usage

To verify one or more modules, use `raco scv` command:

    raco scv paths/to/files.rkt ...

### Non-standard construct

Using non-standard constructs require `fake-contract`:

    (require soft-contract/fake-contract)

#### Termination enforcing

Annotating function contracts with `#:total? #t` enforces
[size-change termination](https://en.wikipedia.org/wiki/Size-change_termination_principle),
where the well-founded partial order is defined on integers (by absolute values) and (immutable) structs and pairs.

```racket
#lang racket/base
(require soft-contract/fake-contract)

(define (fact n)
  (if (zero? n) 1 (* n (fact (sub1 n)))))

(provide/contract
  [f (exact-nonnegative-integer? . -> . exact-nonnegative-integer? #:total? #t)])
```
