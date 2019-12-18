#!/bin/bash

THIS_DIR=$(cd $(dirname $0) && pwd);
$THIS_DIR/gradlew -p $THIS_DIR installDist

if [[ ! -d $HOME/jdk8 ]]; then
	curl -L "https://github.com/AdoptOpenJDK/openjdk8-binaries/releases/download/jdk8u232-b09/OpenJDK8U-jdk_x64_linux_hotspot_8u232b09.tar.gz" > /tmp/jdk.tar.gz;
	mkdir -p $HOME/jdk8;
	tar xf -C $HOME/jdk8 /tmp/jdk.tar.gz;
fi

python $THIS_DIR/integration-test.py $HOME/jdk8/jdk8u232-b09
