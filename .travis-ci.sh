#!/bin/bash

set -ev

opam init --yes --no-setup --comp 4.03.0
eval $(opam config env)
opam install --yes menhir ppx_sexp_conv sexplib

mkdir -p ~/.local/bin
export PATH=$HOME/.local/bin:$PATH
curl -L https://github.com/Z3Prover/z3/releases/download/z3-4.8.4/z3-4.8.4.d6df51951f4c-x64-ubuntu-14.04.zip > z3.zip
unzip -j z3.zip z3-4.8.4.d6df51951f4c-x64-ubuntu-14.04/bin/z3 -d ~/.local/bin

bash ./src/test_suite.sh
