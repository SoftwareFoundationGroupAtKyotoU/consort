#!/bin/bash

THIS_DIR=$(cd $(dirname $0) && pwd)

CLASS_DIR=$THIS_DIR/tmp

if [[ ! -d $CLASS_DIR ]]; then
	mkdir $CLASS_DIR
fi

for i in $THIS_DIR/*.java; do
	rm -f $CLASS_DIR/*;
	if [[ $(basename $i) = "Havoc_Class.java" ]]; then
		continue
	fi
	javac -sourcepath $THIS_DIR -d $CLASS_DIR $i;
	rm $CLASS_DIR/Havoc_Class.class;
	echo Testing $(basename $i);
	java -jar $1 -bounded-heap-size 6 -j $CLASS_DIR
done
