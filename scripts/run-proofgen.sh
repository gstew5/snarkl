#!/bin/bash

# This script generates, from an input R1CS configuration, a proving
# key and a verification key. It then uses libsnark to generate a
# proof for the R1CS, given a satisfying assignment. Finally, it runs
# the libsnark verifier on the resulting proof file and reports the
# result.

# All libsnark output is redirected to LOG.

# Exit codes:
# 1: not enough arguments
# 2: a required file didn't exist
# 3: key-generation failed
# 4: proof-generation failed
# 5: verification failed

LOG=run-r1cs.log

snarky=../cppsrc/bin/snarky

if [ "$#" -lt 3 ]; then
	echo "not enough arguments: 
Arguments:
1- R1CS configuration file
2- input assignment file
3- witness assignment file
"
	exit 1
fi

exec 3>&1 1>${LOG} 2>&1

global_file=""

# create a fresh file in /tmp
fresh_file_name()
{
    UNIQUE=`date +%s%N | sha256sum | base64 | head -c 24`
    fileName="/tmp/snarkl-file-$UNIQUE"
    touch $fileName
    global_file=$fileName
}

ensure_file_exists()
{
    if [ ! -f $1 ]; then 
	echo "file $1 doesn't exist"
	exit 2
    fi
}

R1CS=$1
echo "R1CS file: $R1CS"
fresh_file_name
PK="$global_file"
echo "PK file: $PK"
fresh_file_name
VK="$global_file"
echo "VK file: $VK"
INPUT=$2
echo "Input file: $INPUT"
WITNESS=$3
echo "Witness file: $WITNESS"
fresh_file_name
PROOF="$global_file"
echo "Proof file: $PROOF"

ensure_file_exists $R1CS
ensure_file_exists $INPUT
ensure_file_exists $WITNESS

touch $PK $VK $PROOF

echo "Generating Keys"
time $snarky --generateKeys --csFile $R1CS --verificationKeyFile $VK --provingKeyFile $PK
if [[ $? != 0 ]]; then
    echo "Key-generation Failed!" 1>&3
    exit 3
fi

echo "Generating Proof"
time $snarky --prove --provingKeyFile $PK --inputFile $INPUT \
        --witnessFile $WITNESS --proofFile $PROOF
if [[ $? != 0 ]]; then
    echo "Proof-generation Failed!" 1>&3
    exit 4
fi
