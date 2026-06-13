#!/bin/bash

#SBATCH --time=24:00:00
#SBATCH --nodes=1
#SBATCH --ntasks=1
#SBATCH --cpus-per-task=24
#SBATCH --partition=haswell
#SBATCH --mem-per-cpu=5000M
#SBATCH --output=/scratch/ws/0/s8179597-ws_tripolys/polymorphism_%a.output
#SBATCH -J "polymorphism"
#SBATCH -A p_hardtrees
#SBATCH --array=1-8

INPUT=/scratch/ws/0/s8179597-ws_tripolys/data/10/core_trees.edges
RESULTS=/scratch/ws/0/s8179597-ws_tripolys/results
ARRAY_SIZE=8

mkdir -p $RESULTS

TOTAL=$(wc -l < $INPUT)
CHUNK_SIZE=$(( (TOTAL + ARRAY_SIZE - 1) / ARRAY_SIZE ))
START=$(( (SLURM_ARRAY_TASK_ID - 1) * CHUNK_SIZE + 1 ))
END=$(( START + CHUNK_SIZE - 1 ))

TMPFILE=$(mktemp)
sed -n "${START},${END}p" $INPUT > $TMPFILE

srun ../target/release/polymorphism \
    --condition majority \
    --input $TMPFILE \
    --output $RESULTS/majority_${SLURM_ARRAY_TASK_ID}.csv

rm $TMPFILE
