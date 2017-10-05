#!/bin/bash

echo "Soft typing benchmarks:"
racket soft-contract/test/gen-table.rkt soft-contract/test/programs/safe/softy

echo "Occurence typing benchmarks:"
racket soft-contract/test/gen-table.rkt soft-contract/test/programs/safe/octy

echo "Higher-order model checking benchmarks:"
racket soft-contract/test/gen-table.rkt soft-contract/test/programs/safe/mochi

echo "Higher-order symbolic execution benchmarks:"
racket soft-contract/test/gen-table.rkt soft-contract/test/programs/safe/games

echo "Higher-order stateful benchmarks from different sources:"
#racket test/gen-table.rkt test/programs/safe/real
