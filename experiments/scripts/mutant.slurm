#!/bin/bash
#SBATCH -J mutant
#SBATCH -c 1
#SBATCH --time=0:05:00
#SBATCH --mem=100M
#SBATCH --output=mutant_%A_%a.out

if [[ -z $program ]]; then
    echo Usage: sbatch --export=program=program_file mutant.slurm
    exit
fi

if [ -z "$SLURM_ARRAY_TASK_COUNT" ]; then
    LINE_COUNT=$(wc -l < targets.csv)
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
touch ../data/mutants-data.csv
IFS=','

# --------------------------------------------------------------------
# Mutant generation
# --------------------------------------------------------------------
target=$(cat targets.csv | sed -n $SLURM_ARRAY_TASK_ID'p')
read -ra target_args <<< "$target"
pos=${target_args[0]}
op=${target_args[1]}
arg=${target_args[2]}

output=""
mutant_file_name=""
mutant_file_name_with_ext=""
base_file_name=$(basename $program .dfy)
if [[ -z $arg ]];
then
    echo Mutating position $pos: operator $op
    mutant_file_name=$base_file_name'_'$pos'_'$op
    mutant_file_name_with_ext=$mutant_file_name'.dfy'
    mkdir $mutant_file_name # move job to dir isolated from remaining jobs
    cd $mutant_file_name
    cp ../helpers.txt ./
    output=$({ time dotnet ../$MUTDAFNY_DIR/dafny/Binaries/Dafny.dll verify ../$program \
        --allow-warnings --solver-path ../$MUTDAFNY_DIR/dafny/Binaries/z3 \
        --plugin ../$MUTDAFNY_DIR/mutdafny/bin/Debug/net8.0/mutdafny.dll,"mut $pos $op"; } 2>&1)
else
    echo Mutating position $pos: operator $op, argument $arg
    mutant_file_name=$base_file_name'_'$pos'_'$op'_'$arg
    mutant_file_name_with_ext=$mutant_file_name'.dfy'
    mkdir $mutant_file_name # move job to dir isolated from remaining jobs
    cd $mutant_file_name
    cp ../helpers.txt ./
    output=$({ time dotnet ../$MUTDAFNY_DIR/dafny/Binaries/Dafny.dll verify ../$program \
        --allow-warnings --solver-path ../$MUTDAFNY_DIR/dafny/Binaries/z3 \
        --plugin ../$MUTDAFNY_DIR/mutdafny/bin/Debug/net8.0/mutdafny.dll,"mut $pos $op $arg"; } 2>&1)
fi

# --------------------------------------------------------------------
# Categorize mutant and extract data
# --------------------------------------------------------------------
total_mutation_time=$(echo $output | grep real.*s | awk '{print $2}')
verification_finished=$(echo $output | grep "Dafny program verifier finished")
verified=$(echo $output | grep "Dafny program verifier finished.*0 errors")
timed_out=$(echo $output | grep "Dafny program verifier finished.*time out")
output=$(echo $output | tail -5 | head -1)
status=""

COLOR='\033[0;31m'; if [[ -n $verified ]]; then COLOR='\033[0m'; fi
echo -e "${COLOR}${output}\033[0m"
if [[ -z $verification_finished ]]; then # verification did not finish due to invalid program
    echo Error: mutant is invalid
else
    output_dir=""
    if [[ -n $timed_out ]]; then
        echo Verification timed out
        output_dir=../../mutants/timed-out
        status="T"
    elif [[ -n $verified ]]; then
        echo Verification succeeded: mutant is alive
        output_dir=../../mutants/alive
        status="A"
    else
        echo Verification failed: mutant was killed
        output_dir=../../mutants/killed
        status="K"
    fi
    mv $mutant_file_name_with_ext $output_dir
fi

if [[ -n $verification_finished ]]; then
    parsing_time=$(cat elapsed-time.txt | sed -n '1p' | awk '{print $3}')
    plugin_time=$(cat elapsed-time.txt | sed -n '2p' | awk '{print $3}')
    resolution_time=$(cat elapsed-time.txt | sed -n '3p' | awk '{print $3}')
    verification_time=$(cat elapsed-time.txt | sed -n '4p' | awk '{print $3}')
    echo $mutant_file_name_with_ext $op $total_mutation_time $parsing_time $plugin_time $resolution_time $verification_time $status
    ( flock -x 200
    echo $mutant_file_name_with_ext $op $total_mutation_time $parsing_time $plugin_time $resolution_time $verification_time $status >> ../../data/mutants-data.csv
    ) 200>>../../data/mutants-data.csv
fi
cd ..
rm -rf $mutant_file_name
