#!/bin/sh
var=$(cat $1 | grep $2 | sed "s/.*:= *\(.*\);.*/\1/")
fc=$(echo $var | cut -c 1)
if [ $fc == "X" ]; then
    var=$(echo $var | sed "s/X\"\([A-Fa-f0-9]*\)\"/0x\1/")
else
    var=$(echo $var | sed "s/\"//g")
fi
echo $var
