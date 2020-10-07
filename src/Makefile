.PHONY: all test clean

all: stdlib/lin.intr
	dune build test.exe
	dune build counterexample.exe
	dune build test_suite.exe
	dune build ownership.exe
	dune build counterexampleOwnership.exe

test: all

stdlib/lin.intr stdlib/lin-std.smt: ./genLin.ml
	dune build ./genLin.exe
	dune exec ./genLin.exe stdlib/lin.intr lin-std.smt

%.exe: %.ml
	dune build ./$@

%.a:
	dune build $@

clean:
	dune clean
	rm -f stdlib/lin.intr
