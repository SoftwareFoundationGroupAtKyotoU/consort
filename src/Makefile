.PHONY: all test clean doc

all: stdlib/lin.intr
	dune build test.exe
	dune build test_suite.exe
	dune build genFlags.exe

test: all

stdlib/lin.intr stdlib/lin-std.smt: ./genLin.ml
	dune build ./genLin.exe
	dune exec ./genLin.exe stdlib/lin.intr lin-std.smt

%.exe: %.ml
	dune build ./$@

%.a:
	dune build $@

doc:
	dune build @doc-private
	@echo "See _build/default/_doc/_html"

clean:
	dune clean
	rm -f stdlib/lin.intr
