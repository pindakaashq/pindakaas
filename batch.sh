#!/usr/bin/env bash
id=$(printf "%0${#SLURM_ARRAY_TASK_MAX}d" ${SLURM_ARRAY_TASK_ID})
echo "BATCH.SH START $1:$id (ulimit $2)"
# ( ulimit -v $2 && exec ./target/release/pbc load "$1/$id.json" )
( exec ./target/release/pbc load "$1/$id.json" )
echo "BATCH.SH END $?"

for arg in "$@"
do
	if [[ "$arg" == "--clean" ]]; then
		rm -f $1/../aux/$id.*.dimacs;
		rm -f $1/../aux/$id.*.cnf;
	fi
done


