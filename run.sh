#!/bin/bash
timet=$2

function testAll() {
    for file in $@ -r;do 
        if test -f $file;then 
            echo --------------------------------------------------
            # echo $file
	    cd cdcl_ocac/build/
            start=$[$(date +%s%N)/1000000]
            timeout $timet ./bin/cvc5 ../../$file || { echo "command failed"; }
	    cd ../../
            end=$[$(date +%s%N)/1000000]
            take=$(( end - start ))
            echo $file : ${take} ms.
        fi
        if test -d $file;then
            testAll $file/*
        fi
    done
}

testAll $1
