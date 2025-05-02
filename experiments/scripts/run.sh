#!/bin/bash

DIR=$(cd "$(dirname "$0")" && pwd)
cd "$DIR" &> /dev/null

# --------------------------------------------------------------------
# Set up
# --------------------------------------------------------------------
MUTDAFNY_DIR=../../../mutdafny
rm -rf ../mutants
mkdir ../mutants
mkdir ../mutants/alive
mkdir ../mutants/timed-out
mkdir ../mutants/killed
mkdir ../data
rm ../data/programs-mutation-data.csv
touch ../data/programs-mutation-data.csv
rm ../data/mutants-data.csv
touch ../data/mutants-data.csv
# --------------------------------------------------------------------

scan_args="$*"

programs=(../DafnyBench/DafnyBench/dataset/ground_truth/*.dfy)
for program in "${programs[@]}"
do
    # --------------------------------------------------------------------
    # Scanning
    # --------------------------------------------------------------------
    echo Scanning $program for mutation targets
    output=$({ time dotnet $MUTDAFNY_DIR/dafny/Binaries/Dafny.dll verify $program \
        --allow-warnings --solver-path $MUTDAFNY_DIR/dafny/Binaries/z3 \
        --plugin $MUTDAFNY_DIR/mutdafny/bin/Debug/net8.0/mutdafny.dll,"scan $scan_args" > /dev/null; } 2>&1 &)

    total_scanning_time=$(echo $output | grep real.*s | awk '{print $2}')
    parsing_time1=$(cat elapsed-time.txt | sed -n '1p' | awk '{print $3}')
    plugin_time1=$(cat elapsed-time.txt | sed -n '2p' | awk '{print $3}')
    resolution_time1=$(cat elapsed-time.txt | sed -n '3p' | awk '{print $3}')
    verification_time1=$(cat elapsed-time.txt | sed -n '4p' | awk '{print $3}')

    rm elapsed-time.txt
    # --------------------------------------------------------------------
    # Mutant generation
    # --------------------------------------------------------------------
    number_of_killed_mutants=0
    number_of_alive_mutants=0
    number_of_timed_out_mutants=0

    IFS=','
    readarray -t targets < targets.csv
    for target in "${targets[@]}"
    do
        read -ra target_args <<< "$target"
        pos=${target_args[0]}
        op=${target_args[1]}
        arg=${target_args[2]}

        output=""
        if [[ -z $arg ]]; 
        then 
            echo Mutating position $pos: operator $op
            output=$({ time dotnet $MUTDAFNY_DIR/dafny/Binaries/Dafny.dll verify $program \
                --allow-warnings --solver-path $MUTDAFNY_DIR/dafny/Binaries/z3 \
                --plugin $MUTDAFNY_DIR/mutdafny/bin/Debug/net8.0/mutdafny.dll,"mut $pos $op"; } 2>&1)
        else
            echo Mutating position $pos: operator $op, argument $arg
            output=$({ time dotnet $MUTDAFNY_DIR/dafny/Binaries/Dafny.dll verify $program \
                --allow-warnings --solver-path $MUTDAFNY_DIR/dafny/Binaries/z3 \
                --plugin $MUTDAFNY_DIR/mutdafny/bin/Debug/net8.0/mutdafny.dll,"mut $pos $op $arg"; } 2>&1)
        fi


        mutant_file_name=$(ls *.dfy)
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
                output_dir=../mutants/timed-out
                number_of_timed_out_mutants=$((number_of_timed_out_mutants + 1))
                status="T"
            elif [[ -n $verified ]]; then 
                echo Verification succeeded: mutant is alive
                output_dir=../mutants/alive
                number_of_alive_mutants=$((number_of_alive_mutants + 1))
                status="A"
            else 
                echo Verification failed: mutant was killed
                output_dir=../mutants/killed
                number_of_killed_mutants=$((number_of_killed_mutants + 1))
                status="K"
            fi
            mv *.dfy $output_dir
        fi

        if [[ -n $verification_finished ]]; then
            parsing_time2=$(cat elapsed-time.txt | sed -n '1p' | awk '{print $3}')
            plugin_time2=$(cat elapsed-time.txt | sed -n '2p' | awk '{print $3}')
            resolution_time2=$(cat elapsed-time.txt | sed -n '3p' | awk '{print $3}')
            verification_time2=$(cat elapsed-time.txt | sed -n '4p' | awk '{print $3}')
            echo $mutant_file_name $op $total_mutation_time $parsing_time2 $plugin_time2 $resolution_time2 $verification_time2 $status >> ../data/mutants-data.csv
        fi
        echo
        rm elapsed-time.txt
    done

    # --------------------------------------------------------------------
    # Save remaining data and clean up
    # --------------------------------------------------------------------
    number_of_targets=$(wc -l targets.csv  | awk '{print $1}')
    number_of_invalid_mutants=$((number_of_targets - number_of_killed_mutants - number_of_alive_mutants - number_of_timed_out_mutants))    

    echo $program $total_scanning_time $parsing_time1 $plugin_time1 $resolution_time1 $verification_time1 $number_of_targets $number_of_killed_mutants $number_of_alive_mutants $number_of_timed_out_mutants $number_of_invalid_mutants >> ../data/programs-mutation-data.csv
    rm targets.csv
    rm helpers.txt
done

cd - &> /dev/null
