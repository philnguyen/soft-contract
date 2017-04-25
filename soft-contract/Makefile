DEFAULT: compile

z3:
	raco pkg install z3

compile:
	raco link .
	@echo "Compiling, will take several minutes..."
	raco make -j $$(nproc) cmdline.rkt

test:
	raco test test/sanity-test.rkt

clean:
	rm -rf $$(find . -type d -name compiled | xargs)
