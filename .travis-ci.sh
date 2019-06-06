#!/bin/bash

set -ev

opam init --yes --no-setup --comp 4.03.0
eval $(opam config env)
opam install --yes menhir ppx_sexp_conv sexplib

bash ./src/test_suite.sh
