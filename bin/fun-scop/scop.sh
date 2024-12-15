#!/bin/bash

#----------------------------
# Args and Commands
#----------------------------
# $1 JVM heap size for encode
# $2 path of scop.jar
# $3 <-hybrid|-order|-log>
# $4 path of satsolver
# $5 satsolver options
# $6 path of tmp dir
# $7 XCSP3 instance

# for test environment to be sure where is lzma
# source /Users/soh/.bash_profile

# name of the saved data
sfile="$6/scop-$$-serial-file.bin"
# name of the CNF
base=`basename $7`
cnf="$6/scop-$$-$base.cnf"

jvmheap_encode="-Xms$1 -Xmx$1"
jvmheap_solve="-Xms4g -Xmx4g"
cmd_encode="java $jvmheap_encode -Xss128m -cp $2 fun.scop.launcher.XCSP19Encode $3 -solver $4 -solverOption $5 -tmp $6 -serialFile $sfile $7"
cmd_solve="java $jvmheap_solve -Xss128m -cp $2 fun.scop.launcher.XCSP19Solve $sfile"

#----------------------------
# logging
#----------------------------
logger () {
    echo "c (scop.sh) $1"
}

#----------------------------
# Signal Handling
#----------------------------
cleanAll () {
    logger "Receiving Signal. Removing all intermediate files."
    status=$?
    if [ -e $sfile ]; then
        logger "Remove $sfile".
        rm $sfile
    fi
    if [ -e $cnf ]; then
        logger "Remove $cnf".
        rm $cnf
    fi
    logger "Killing background jobs."
    kill $(jobs -p)
    exit $status
}

trap cleanAll HUP
trap cleanAll INT
trap cleanAll TERM

#----------------------------
# Encoding
#----------------------------
logger "$cmd_encode"
$cmd_encode &
pid1=$!
wait

#----------------------------
# Solving
#----------------------------
if [ -e $sfile ]; then
    logger "$cmd_solve"
    $cmd_solve &
    pid2=$!
    wait
else
    logger "$sfile does not exist. End.";
fi

exit 0
