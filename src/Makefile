.PHONY: all test clean

all: stdlib/lin.intr
	dune build test.exe
	dune build test.bc
	dune build test_suite.exe
	dune build test_suite.bc

test: all


stdlib/lin.intr: ./genLin.ml
	dune exec ./genLin.exe > stdlib/lin.intr

clean:
	dune clean
	rm -f stdlib/lin.intr
