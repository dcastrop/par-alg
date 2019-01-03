#!/bin/bash

UNROLL=8
MAX_CORES=8

BENCH_DIR=${PWD}
DIRS=$(for i in `seq 0 ${UNROLL}`; do echo "K${i}"; done)
CORES=`seq 1 ${MAX_CORES}`
GHC_OPTS="-threaded -rtsopts"
RTS_OPTS="-A1.5G"
TEST=${BENCH_DIR##*/}
TEST=${TEST%.*}

echo "Generating and compiling"
for DIR in ${DIRS}; do
  pushd ${BENCH_DIR}/${DIR}
  echo ${TEST}
  rm -f *.o
  rm -f *.ho
  rm -f *.hi
  rm Main
  stack build; stack exec -- par-lang -p -a=Atoms.hs ${TEST}.par
  stack exec -- ghc ${GHC_OPTS} Main.hs
  rm -f *.o
  rm -f *.ho
  rm -f *.hi
  popd
done

echo "Running"
pushd ${BENCH_DIR}/Base
stack build; stack exec -- par-lang -p -a=Atoms.hs ${TEST}.par
stack exec -- ghc ${GHC_OPTS} Main.hs
rm -f *.o
rm -f *.ho
rm -f *.hi
tar -cvjpf Measurements.tar.bz2 Measurements
rm -rf ./Measurements
mkdir ./Measurements
echo ${DIR} > ./Measurements/${TEST}_seq.time
for N in ${CORES}; do
  echo  >> ./Measurements/${TEST}_seq.time
  echo "------------ ${N} CORES --------------" >> ./Measurements/${TEST}_seq.time
  echo  >> ./Measurements/${TEST}_seq.time
  ./Main 'seq/' --csv ./Measurements/${TEST}_seq_${N}.csv +RTS ${RTS_OPTS} -N${N} >> ./Measurements/${TEST}_seq.time
  sleep 1
  echo  >> ./Measurements/${TEST}_seq.time
done

echo ${DIR} > ./Measurements/${TEST}_hs.time
for N in ${CORES}; do
  echo  >> ./Measurements/${TEST}_hs.time
  echo "------------ ${N} CORES --------------" >> ./Measurements/${TEST}_hs.time
  echo  >> ./Measurements/${TEST}_hs.time
  ./Main 'hs/' --csv ./Measurements/${TEST}_hs_${N}.csv +RTS ${RTS_OPTS} -N${N} >> ./Measurements/${TEST}_hs.time
  sleep 1
  echo  >> ./Measurements/${TEST}_hs.time
done
popd

for DIR in ${DIRS}; do
  pushd ${BENCH_DIR}/${DIR}
  tar -cvjpf Measurements.tar.bz2 Measurements
  rm -rf ./Measurements
  mkdir ./Measurements
  echo ${DIR} > ./Measurements/${TEST}_par.time
  for N in ${CORES}; do
    echo  >> ./Measurements/${TEST}_par.time
    echo "------------ ${N} CORES --------------" >> ./Measurements/${TEST}_par.time
    echo  >> ./Measurements/${TEST}_par.time
    ./Main 'par/' --csv ./Measurements/${TEST}_par_${N}.csv +RTS ${RTS_OPTS} -N${N} >> ./Measurements/${TEST}_par.time
    sleep 1
    echo  >> ./Measurements/${TEST}_par.time
  done
  popd
done
