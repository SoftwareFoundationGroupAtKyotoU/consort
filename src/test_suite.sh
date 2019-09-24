#!/bin/bash

THIS_DIR=$(cd $(dirname $0) && pwd)

function r_test {
	./_build/default/test_suite.exe -verbose -intrinsics ./stdlib/lin.intr "$@"
}

function jayhorn {
	python ./benchmarks/run_jayhorn.py -timeout 5 -intrinsics ./stdlib/lin.intr "$@"
}

declare -a POS_DIRS
POS_DIRS=(pre-relation challenge-problem jayhorn recursive-tests arrays)
NEG_DIRS=(recursive-tests challenge-problem arrays)

(
	cd $THIS_DIR;
	make test;
	r_test "$@" -timeout 15 -pos ./positive-tests;
	for i in ${POS_DIRS[@]}; do
		r_test "$@" -timeout 60 -pos ./positive-tests/$i;
	done
	r_test "$@" -pos -cfa 2 ./positive-tests/2cfa;
	r_test "$@" -neg ./negative-tests
	for i in ${NEG_DIRS[@]}; do
		r_test "$@" -neg ./negative-tests/$i;
	done
	jayhorn ./benchmarks/jayhorn/Sat*.imp;
	jayhorn -neg ./benchmarks/jayhorn/Unsat*.imp;
)
