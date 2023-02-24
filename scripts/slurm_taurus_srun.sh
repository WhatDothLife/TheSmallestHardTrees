#!/bin/bash

#SBATCH --time=24:00:00   # walltime
#SBATCH --nodes=1   # number of nodes
#SBATCH --ntasks=1      # limit to one node
#SBATCH --cpus-per-task=24  # number of processor cores (i.e. threads)
#SBATCH --partition=haswell
#SBATCH --mem-per-cpu=5000M   # memory per CPU core
#SBATCH --output=/scratch/ws/0/s8179597-ws_tripolys/majority.output
#SBATCH -J "majority"   # job name
#SBATCH -A p_hardtrees

srun ../target/release/examples/tripolys \
    --data_path /scratch/ws/0/s8179597-ws_tripolys/HardTreesData \
	--start 1 \
	--end 20 \
	--core \
