#!/bin/bash

pushd () {
    command pushd "$@" > /dev/null
}

popd () {
    command popd "$@" > /dev/null
}

UNROLL=8
MAX_CORES=8

BENCH_DIR=${1}
DIRS=($(echo "Base"; for i in `seq 0 ${UNROLL}`; do echo "K${i}"; done))
CORES=(`seq 1 ${MAX_CORES}`)

NUMDIRS=${#DIRS[@]}
NUMCORES=${#CORES[@]}
TOTAL_TASKS=$((${NUMDIRS}*${NUMCORES}))

for ((i = 0; i < ${NUMDIRS}; i++)); do
  rm -f ${BENCH_DIR}/${DIRS[${i}]}/Measurements/*
done

TMP=${2}

rm -f ${TMP}
touch ${TMP}

echo "#PBS -lwalltime=8:00:00"                                               >> ${TMP}
echo "#PBS -lselect=1:ncpus=${MAX_CORES}:mem=4gb"                            >> ${TMP}
echo "#PBS -lplace=pack:excl"                                                >> ${TMP}
echo "#PBS -J 1-${TOTAL_TASKS}"                                              >> ${TMP}
echo                                                                         >> ${TMP}
echo "BENCH_DIR=${BENCH_DIR}"                                                >> ${TMP}
echo "NUMDIRS=${NUMDIRS}"                                                    >> ${TMP}
echo "NUMCORES=${NUMCORES}"                                                  >> ${TMP}
echo "DIRS=(${DIRS[*]})"                                                     >> ${TMP}
echo "CORES=(${CORES[*]})"                                                   >> ${TMP}
echo                                                                         >> ${TMP}
echo 'i=$((${PBS_ARRAY_INDEX}-1))'                                           >> ${TMP}
echo 'DIR=${DIRS[$((${i} / ${NUMCORES}))]}'                                  >> ${TMP}
echo 'N=${CORES[$((${i} % ${NUMCORES}))]}'                                   >> ${TMP}
echo                                                                         >> ${TMP}
echo 'cp -r ${PBS_O_WORKDIR}/${BENCH_DIR}/${DIR} .'                          >> ${TMP}
echo 'if [ "${DIR}" = "Base" ]; then BENCHNAME=seq/; else BENCHNAME=par/; fi' >> ${TMP}
echo 'pushd ./${DIR}'                                                        >> ${TMP}
echo './Main ${BENCHNAME} \
-L 60 \
--csv ./Measurements/Time_${N}.csv \
+RTS \
-N${N} > ./Measurements/Time_${N}.time'                                      >> ${TMP}
echo 'popd'                                                                  >> ${TMP}
echo 'cp -r ${DIR} ${PBS_O_WORKDIR}/${BENCH_DIR}'                            >> ${TMP}

cat ${TMP}
qsub -W block=True ${TMP}

echo 
echo
echo "Finished. Press any key to continue"
read

rm -f ${TMP}
rm -f ${TMP}.e*
rm -f ${TMP}.o*

for ((i = 0; i < ${NUMDIRS}; i++))
do
  pushd ${BENCH_DIR}/${DIRS[${i}]}/Measurements
  RESFILE=${BENCH_DIR%/}.time
  rm -f *.csv
  rm -f ${RESFILE}
  touch ${RESFILE}
  for ((j = 0; j < ${NUMCORES}; j++))
  do
    N=${CORES[${j}]}
    echo                                          >> ${RESFILE}
    echo "------------ ${N} CORES --------------" >> ${RESFILE}
    [ -f Time_${N}.time ] && cat Time_${N}.time   >> ${RESFILE}
    rm -f Time_${N}.time
    echo                                          >> ${RESFILE}
  done
  popd
done
