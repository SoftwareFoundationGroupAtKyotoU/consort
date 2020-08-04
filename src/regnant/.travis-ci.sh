#!/bin/bash

set -ev

THIS_DIR=$(cd $(dirname $0) && pwd);
$THIS_DIR/gradlew --console plain -p $THIS_DIR installDist

if [[ ! -d $HOME/jdk8/jdk8u232-b09 ]]; then
        curl -L "https://github.com/AdoptOpenJDK/openjdk8-binaries/releases/download/jdk8u232-b09/OpenJDK8U-jdk_x64_linux_hotspot_8u232b09.tar.gz" > /tmp/jdk.tar.gz;
        mkdir -p $HOME/jdk8;
        tar xf /tmp/jdk.tar.gz -C $HOME/jdk8;
fi

pip3 install PyYaml
python3 $THIS_DIR/integration-test.py $HOME/jdk8/jdk8u232-b09
