#!/bin/bash

pushd () {
    command pushd "$@" > /dev/null
}

popd () {
    command popd "$@" > /dev/null
}

UNROLL=8
MAX_CORES=24

BENCH_DIR=${1}
DIRS=($(echo "Base"; for i in `seq 0 ${UNROLL}`; do echo "K${i}"; done))
CORES=(`seq 1 ${MAX_CORES}`)

NUMDIRS=${#DIRS[@]}
NUMCORES=${#CORES[@]}

for ((i = 0; i < ${NUMDIRS}; i++)); do
  rm -f ${BENCH_DIR}/${DIRS[${i}]}/Measurements/*
done

TMP=${2}

[ -f ${TMP} ] && echo "${2} already exists" && exit 1

echo "Compiling ${BENCH_DIR}"
pushd ${BENCH_DIR}
./compile.sh
popd

for ((i = 0; i < ${MAX_CORES}; i++))
do
  C=${CORES[${i}]}

  rm -f ${TMP}
  touch ${TMP}

  echo "#!/bin/bash"                                                            >> ${TMP}
  echo "#PBS -lwalltime=2:00:00"                                                >> ${TMP}
  echo "#PBS -lselect=1:ncpus=32:mem=8gb"                                       >> ${TMP}
  echo "#PBS -lplace=pack:excl"                                                 >> ${TMP}
  echo "#PBS -J 1-${NUMDIRS}"                                                   >> ${TMP}
  echo                                                                          >> ${TMP}
  echo "BENCH_DIR=${BENCH_DIR}"                                                 >> ${TMP}
  echo "NUMDIRS=${NUMDIRS}"                                                     >> ${TMP}
  echo "DIRS=(${DIRS[*]})"                                                      >> ${TMP}
  echo                                                                          >> ${TMP}
  echo 'i=$((${PBS_ARRAY_INDEX}-1))'                                            >> ${TMP}
  echo 'DIR=${DIRS[${i}]}'                                                      >> ${TMP}
  echo "N=${C}"                                                                 >> ${TMP}
  echo                                                                          >> ${TMP}
  echo 'cp -r ${PBS_O_WORKDIR}/${BENCH_DIR}/${DIR} .'                           >> ${TMP}
  echo 'BENCHNAME=par/'                                                         >> ${TMP}
  echo '[ "${DIR}" = "Base" ] && BENCHNAME=seq/'                                >> ${TMP}
  echo 'pushd ./${DIR}'                                                         >> ${TMP}
  echo './Main ${BENCHNAME} \
  -L 180 \
  --csv ./Measurements/Time_${N}.csv \
  +RTS \
  -N${N} > ./Measurements/Time_${N}.time'                                       >> ${TMP}
  echo 'popd'                                                                   >> ${TMP}
  echo 'cp -r ${DIR}/Measurements ${PBS_O_WORKDIR}/${BENCH_DIR}/${DIR}'         >> ${TMP}

  echo "PBS Script:"
  echo "============================================"
  cat ${TMP}
  echo "============================================"

  echo "Enqueuing tasks:"
  qsub -W block=True ${TMP}
done


for ((i = 0; i < ${NUMDIRS}; i++))
do
  pushd ${BENCH_DIR}/${DIRS[${i}]}/Measurements
  RESFILE=${BENCH_DIR%/}.time
  rm -f *.csv
  rm -f ${RESFILE}
  touch ${RESFILE}
  echo ${DIRS[${i}]}                              >> ${RESFILE}
  echo                                            >> ${RESFILE}
  for ((j = 0; j < ${NUMCORES}; j++))
  do
    N=${CORES[${j}]}
    echo                                          >> ${RESFILE}
    echo "------------ ${N} CORES --------------" >> ${RESFILE}
    echo                                          >> ${RESFILE}
    [ -f Time_${N}.time ] && cat Time_${N}.time   >> ${RESFILE}
    echo                                          >> ${RESFILE}
  done
  popd
done
