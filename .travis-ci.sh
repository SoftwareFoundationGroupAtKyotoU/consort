#!/bin/bash

set -ev

opam init --yes --no-setup --comp 4.08.0
eval $(opam config env)
opam install --yes menhir ppx_sexp_conv sexplib dune ppx_let ppx_custom_printf yaml
travis_wait 30 install --yes z3

mkdir -p ~/.local/bin
export PATH=$HOME/.local/bin:$PATH
# curl -L https://github.com/Z3Prover/z3/releases/download/z3-4.8.12/z3-solver-4.8.12.0.tar.gz > z3.tar.gz
# unzip -o -j z3.zip z3-4.8.12-x64-glibc-2.31/bin/z3 -d ~/.local/bin

z3 -version

# approximately the memory available on travis
make -C ./src test.exe genFlags.exe stdlib/lin.intr
bash ./src/test_suite.sh -solver-args "-memory:6000"

bash ./src/regnant/.travis-ci.sh
