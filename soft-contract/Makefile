all: test

test:
	@echo "Outputting static checker's result on tests"
	@echo "========================================="
	@for file in tests/*.rkt; \
        do \
	    echo "## checking $$file"; \
	    raco scv "$$file"; \
	done;
