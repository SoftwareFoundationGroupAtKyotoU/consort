#!/bin/bash

BDIR=$(mktemp -d --suff="consort")

USR=$(whoami)
if [[ $# -gt 0 ]]; then
	USR=$1
fi

THIS_DIR=$(cd $(dirname $0) && pwd)
SRC_DIR=$THIS_DIR/../src

mkdir -p $BDIR/consort
mkdir -p $BDIR/consort/benchmarks
mkdir -p $BDIR/consort/benchmarks/consort/java

cp -r $SRC_DIR/*.ml* $SRC_DIR/*.sh $SRC_DIR/dune $SRC_DIR/Makefile $SRC_DIR/dune-project $SRC_DIR/with_monad $SRC_DIR/stdlib $SRC_DIR/config.yml $BDIR/consort
cp -r $SRC_DIR/negative-tests $SRC_DIR/positive-tests $BDIR/consort

cp -r $SRC_DIR/benchmarks/jayhorn $BDIR/consort/benchmarks

cp -r $SRC_DIR/benchmarks/consort/* $BDIR/consort/benchmarks/consort/java

python $THIS_DIR/collect_tests.py $BDIR/consort/config.yml

(cd $BDIR; tar cf consort.tar.bz2 -j consort);

SHA=$(md5sum $BDIR/consort.tar.bz2 | awk '{print $1}')

kramdown $THIS_DIR/index.md > $THIS_DIR/index.html.en

sed -i -e "s/HASH_OF_ARCHIVE/$SHA/" $THIS_DIR/index.html.en

scp $THIS_DIR/index.html.en $THIS_DIR/*.css $BDIR/consort.tar.bz2 $USR@io.kuis.kyoto-u.ac.jp:/var/www/public/projects/consort/

#rm -rf $BDIR
echo $BDIR
