.PHONY: all test

all:
	dune build test.exe
	dune build test.bc
	dune build test_suite.exe
	dune build test_suite.bc

test: all stdlib/lin.intr


stdlib/lin.tr: ./genLin.ml
	dune exec ./genLin.exe > stdlib/lin.intr

