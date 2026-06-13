#!/bin/bash

#SBATCH --time=00:10:00
#SBATCH --nodes=1
#SBATCH --ntasks=1
#SBATCH --cpus-per-task=1
#SBATCH --partition=haswell
#SBATCH --mem-per-cpu=1000M
#SBATCH --output=/scratch/ws/0/s8179597-ws_tripolys/polymorphism_merge.output
#SBATCH -J "polymorphism_merge"
#SBATCH -A p_hardtrees

RESULTS=/scratch/ws/0/s8179597-ws_tripolys/results
OUTPUT=$RESULTS/majority.csv

# write header from first chunk
head -n 1 $RESULTS/majority_1.csv > $OUTPUT

# append data rows from all chunks (skip header)
for f in $RESULTS/majority_*.csv; do
    tail -n +2 $f >> $OUTPUT
done

# clean up chunks
rm $RESULTS/majority_*.csv
