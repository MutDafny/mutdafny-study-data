#!/bin/bash
#SBATCH -J scan
#SBATCH -c 1
#SBATCH --time=0:05:00
#SBATCH --mem=100M
#SBATCH --output=logs/scan_%A_%a.out

if [[ -z $op ]]; then
    echo Usage: sbatch --export=op=mutation_operator scan.slurm
    exit
fi

PROGRAMS_DIR=../DafnyBench/DafnyBench/dataset/ground_truth
if [ -z "$SLURM_ARRAY_TASK_COUNT" ]; then
    LINE_COUNT=$(ls $PROGRAMS_DIR | wc -l)
    ARRAY_MAX=$((LINE_COUNT))
    # Re-submit with proper array range
    sbatch --array=1-${ARRAY_MAX} $0
    exit
fi


MUTDAFNY_DIR=../../../mutdafny
mkdir ../mutants
mkdir ../mutants/alive
mkdir ../mutants/timed-out
mkdir ../mutants/killed
mkdir ../data
touch ../data/programs-mutation-data.csv

# --------------------------------------------------------------------
# Scan program for mutation targets
# --------------------------------------------------------------------
file_name_with_ext=$(ls $PROGRAMS_DIR | sed -n $SLURM_ARRAY_TASK_ID'p')
file_name=$(basename $file_name_with_ext .dfy)
program=$PROGRAMS_DIR/$file_name_with_ext
mkdir tmp_$file_name # move job to dir isolated from remaining jobs
cd tmp_$file_name

echo Scanning $program for mutation targets
output=$({ time dotnet ../$MUTDAFNY_DIR/dafny/Binaries/Dafny.dll verify ../$program \
        --allow-warnings --solver-path ../$MUTDAFNY_DIR/dafny/Binaries/z3 \
        --plugin ../$MUTDAFNY_DIR/mutdafny/bin/Debug/net8.0/mutdafny.dll,"scan $op"; } 2>&1)

total_scanning_time=$(echo $output | grep -o real.*s | awk '{print $2}')
parsing_time=$(cat elapsed-time.txt | sed -n '1p' | awk '{print $3}')
plugin_time=$(cat elapsed-time.txt | sed -n '2p' | awk '{print $3}')
resolution_time=$(cat elapsed-time.txt | sed -n '3p' | awk '{print $3}')
verification_time=$(cat elapsed-time.txt | sed -n '4p' | awk '{print $3}')
number_of_targets=$(cat targets.csv | wc -l)

# --------------------------------------------------------------------
# Generate mutants through new job array submission
# --------------------------------------------------------------------
echo Generating mutants of $program
SLURM_ARRAY_TASK_COUNT="" # reset
sbatch --export=program=$program ../mutant.slurm
echo $file_name_with_ext $total_scanning_time $parsing_time $plugin_time $resolution_time $verification_time $number_of_targets
( flock -x 200
echo $file_name_with_ext $total_scanning_time $parsing_time $plugin_time $resolution_time $verification_time $number_of_targets >> ../../data/programs-mutation-data.csv
) 200>>../../data/programs-mutation-data.csv

cd ..
