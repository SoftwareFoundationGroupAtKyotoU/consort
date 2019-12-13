#!/bin/bash

wget http://services.gradle.org/distributions/gradle-4.0.1-bin.zip
unzip gradle-4.0.1-bin.zip
export GRADLE_HOME=$PWD/gradle-4.0.1
export PATH=$GRADLE_HOME/bin:$PATH

gradle allDeps
