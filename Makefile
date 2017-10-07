all: test tables proof

test:
	@echo "Running sanity test suite"
	@raco test soft-contract/test/sanity-test.rkt

tables:
	@echo "Generating benchmark tables"
	@echo ""
	@echo "Soft typing benchmarks:"
	@racket soft-contract/test/gen-table.rkt soft-contract/test/programs/safe/softy
	@echo "Occurence typing benchmarks:"
	@racket soft-contract/test/gen-table.rkt soft-contract/test/programs/safe/octy
	@echo "Higher-order model checking benchmarks:"
	@racket soft-contract/test/gen-table.rkt soft-contract/test/programs/safe/mochi
	@echo "Higher-order symbolic execution benchmarks:"
	@racket soft-contract/test/gen-table.rkt soft-contract/test/programs/safe/games
	@echo "Higher-order stateful benchmarks from different sources:"
	@racket soft-contract/test/gen-table.rkt soft-contract/test/programs/safe/real

proof:
	lean mechanized/*.lean
