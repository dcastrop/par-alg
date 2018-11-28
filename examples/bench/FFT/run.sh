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
  stack build; stack exec -- par-lang -p -a=Atoms.hs ${TEST}.par
  stack exec -- ghc ${GHC_OPTS} Main.hs
  rm -f *.o
  rm -f *.ho
  rm -f *.hi
  popd
done

echo "Running"
for DIR in ${DIRS}; do
  pushd ${BENCH_DIR}/${DIR}
  tar -cvjpf Measurements.tar.bz2 Measurements
  rm -rf ./Measurements
  mkdir ./Measurements
  echo ${DIR} > ./Measurements/${TEST}_par.time
  echo ${DIR} > ./Measurements/${TEST}_seq.time
  for N in ${CORES}; do
    echo  >> ./Measurements/${TEST}_seq.time
    echo  >> ./Measurements/${TEST}_par.time
    echo "------------ ${N} CORES --------------" >> ./Measurements/${TEST}_par.time
    echo "------------ ${N} CORES --------------" >> ./Measurements/${TEST}_seq.time
    echo  >> ./Measurements/${TEST}_seq.time
    echo  >> ./Measurements/${TEST}_par.time
    ./Main 'par/' --csv ./Measurements/${TEST}_par_${N}.csv +RTS -N${N} >> ./Measurements/${TEST}_par.time
    sleep 1
    ./Main 'seq/' --csv ./Measurements/${TEST}_seq_${N}.csv +RTS -N${N} >> ./Measurements/${TEST}_seq.time
    sleep 1
    echo  >> ./Measurements/${TEST}_par.time
    echo  >> ./Measurements/${TEST}_seq.time
  done
  popd
done

