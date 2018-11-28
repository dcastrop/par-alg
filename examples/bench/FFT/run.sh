#!/bin/bash

UNROLL=8
MAX_CORES=8

BENCH_DIR=${PWD}
DIRS=$(for i in `seq 0 ${UNROLL}`; do echo "K${i}"; done)
CORES=`seq 1 ${MAX_CORES}`
GHC_OPTS="-threaded -O"
TEST=${BENCH_DIR##*/}
TEST=${TEST%.*}

echo "Generating and compiling"
for DIR in ${DIRS}; do
  pushd ${BENCH_DIR}/${DIR}
  echo ${TEST}
  stack build; stack exec -- par-lang -p ${TEST}.par
  stack exec -- ghc ${GHC_OPTS} Main.hs
  rm -f *.o
  rm -f *.ho
  rm -f *.hi
  popd
done

echo "Running"
for DIR in ${DIRS}; do
  pushd ${BENCH_DIR}/${DIR}
  echo ${DIR} > ${TEST}_par.time
  echo ${DIR} > ${TEST}_seq.time
  for N in ${CORES}; do
    echo  >> ${TEST}_seq.time
    echo "------------ ${N} CORES -------------- >> ${TEST}_par.time
    echo "------------ ${N} CORES -------------- >> ${TEST}_seq.time
    echo  >> ${TEST}_par.time
    sleep 1
    ./Main 'par/' -v 2 --template json --output ${TEST}_par_${N}.json +RTS -N${N} >> ${TEST}_par.time
    sleep 1
    ./Main 'seq/' -v 2 --template json --output ${TEST}_seq_${N}.json +RTS -N${N} >> ${TEST}_seq.time
    echo  >> ${TEST}_par.time
    echo  >> ${TEST}_seq.time
  done
  popd
done

