#!/bin/bash
rm -f release/lib/AppleJavaExtensions.jar
java -cp release/lib/*:release/jHOLLib.jar edu.pitt.math.jhol.HOLLightWrapper `whoami`
