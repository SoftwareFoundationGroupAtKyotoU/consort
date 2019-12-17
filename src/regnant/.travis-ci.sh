#!/bin/bash

THIS_DIR=$(cd $(dirname $0) && pwd);
(cd $THIS_DIR; ./gradlew installDist)
