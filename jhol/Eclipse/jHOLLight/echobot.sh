#!/bin/bash
rm release/lib/AppleJavaExtensions.jar
java -cp release/lib/*:release/jHOLLib.jar edu.pitt.math.jhol.irc.EchoBot
