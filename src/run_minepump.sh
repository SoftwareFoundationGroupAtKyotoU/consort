#!/bin/bash

if [[ $# -lt 2 ]]; then
	echo "Need minepump folder and jayhorn";
	exit 1
fi

for i in $1/*; do
	echo $i;
	pushd $i;
	if [[ ! -d tmp ]]; then
		mkdir tmp
	fi
	javac ./Main.java -d tmp;
	popd;
	timeout 60s java -jar $2 -j $i/tmp > /dev/null 2> /dev/null
	if [[ $? -eq 124 ]]; then
		echo "TIMEOUT";
	else
		echo "NO timeout";
	fi
done
