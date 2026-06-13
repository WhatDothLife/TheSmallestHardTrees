#!/bin/bash

#SBATCH --time=24:00:00
#SBATCH --nodes=1
#SBATCH --ntasks=1
#SBATCH --cpus-per-task=24
#SBATCH --partition=haswell
#SBATCH --mem-per-cpu=5000M
#SBATCH --output=/scratch/ws/0/s8179597-ws_tripolys/polymorphism.output
#SBATCH -J "polymorphism"
#SBATCH -A p_hardtrees

srun ../target/release/polymorphism \
    --condition majority \
    --input /scratch/ws/0/s8179597-ws_tripolys/data/trees.edges \
    --output /scratch/ws/0/s8179597-ws_tripolys/results.csv
