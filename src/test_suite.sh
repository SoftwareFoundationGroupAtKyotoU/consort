#!/bin/bash

THIS_DIR=$(cd $(dirname $0) && pwd)

(
	cd $THIS_DIR;
	make;
	dune exec ./test_suite.exe -- -pos ./positive-tests
	dune exec ./test_suite.exe -- -neg ./negative-tests
)
