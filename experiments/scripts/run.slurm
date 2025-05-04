#!/bin/bash
#SBATCH -J mutdafny
#SBATCH -c 1
#SBATCH --time=3:00:00
#SBATCH --mem=100M
#SBATCH --output=logs/mutdafny_%A_%a.out

if [[ -z $op ]]; then
    echo Usage: sbatch --export=op=mutation_operator run.slurm
    exit
fi


sbatch --export=op=$op scan.slurm

number_of_jobs_running=$(squeue | grep -E "mutdafny|scan|mutant" | wc -l)
while [[ $number_of_jobs_running -ne 1 ]]
do
    number_of_jobs_running=$(squeue | grep -E "mutdafny|scan|mutant" | wc -l)
done
echo Finished all jobs

# --------------------------------------------------------------------
# Extract data
# --------------------------------------------------------------------
touch complete_data.csv
echo program total_scan_time parse_time plugin_time res_time verif_time num_targets num_killed num_alive num_time_out num_inv > complete_data.csv

readarray -t entries < ../data/programs-mutation-data.csv
for entry in "${entries[@]}" 
do
    file_name_with_ext=$(echo $entry | awk '{print $1}')
    file_name=$(basename $file_name_with_ext .dfy)
    number_of_targets=$(echo $entry | awk '{print $7}')
    number_of_killed_mutants=$(ls ../mutants/killed | grep $file_name | wc -l)
    number_of_alive_mutants=$(ls ../mutants/alive | grep $file_name | wc -l)
    number_of_timed_out_mutants=$(ls ../mutants/timed-out | grep $file_name | wc -l)
    number_of_invalid_mutants=$((number_of_targets - number_of_killed_mutants - number_of_alive_mutants - number_of_timed_out_mutants))
    echo $entry $number_of_killed_mutants $number_of_alive_mutants $number_of_timed_out_mutants $number_of_invalid_mutants >> complete_data.csv
done

cat complete_data.csv > ../data/programs-mutation-data.csv
rm complete_data.csv
rm -rf tmp_*
