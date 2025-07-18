#!/usr/bin/env bash
#
# ------------------------------------------------------------------------------
# Given a list of the generated mutants (i.e., mut-data.csv), this script
# joins this data with data regarding the number of pre and postconditions of the method/function under mutation
# and collects all of the alive mutants whose mutations were applied in methods with at least one postcondition.
# The script generates a directory with the mutants that fit these conditions.
#
# Usage:
# filter-mutants.sh
#   --input_mutants_file <full path to the list of generated mutants, e.g., $SCRIPT_DIR/../data/generated/mut-data.csv
#   --input_methods_file <full path to the list of generated mutants, e.g., $SCRIPT_DIR/../data/generated/methods-data.csv
#   --input_mutants_dir_path <full path to the directory containing the mutants, e.g., $SCRIPT_DIR/../data/generated/mut
#   --output_data_dir_path <full path, e.g., $SCRIPT_DIR/../data/generated/
#   --output_mutants_dir_path <full path, e.g., $SCRIPT_DIR/../data/generated/mut/filtered
#   [help]
# ------------------------------------------------------------------------------

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" > /dev/null 2>&1 && pwd)"
source "$SCRIPT_DIR/../../utils/scripts/utils.sh" || exit 1

# ------------------------------------------------------------------------- Args

USAGE="Usage: ${BASH_SOURCE[0]} \
  --input_mutants_file <full path to the list of generated mutants, e.g., $SCRIPT_DIR/../data/generated/mut-data.csv>
  --input_methods_file <full path to the list of generated mutants, e.g., $SCRIPT_DIR/../data/generated/methods-data.csv>
  --input_mutants_dir_path <full path to the directory containing the mutants, e.g., $SCRIPT_DIR/../data/generated/mut>
  --output_data_dir_path <full path, e.g., $SCRIPT_DIR/../data/generated/>
  --output_mutants_dir_path <full path, e.g., $SCRIPT_DIR/../data/generated/mut/filtered>
  [help]"
if [ "$#" -ne "1" ] && [ "$#" -ne "10" ]; then
  die "$USAGE"
fi

# Print out script's arguments (which could help any debug session)
echo "[INFO] ${BASH_SOURCE[0]} $@"

INPUT_MUTANTS_FILE=""
INPUT_METHODS_FILE=""
INPUT_MUTANTS_DIR_PATH=""
OUTPUT_DATA_DIR_PATH=""
OUTPUT_MUTANTS_DIR_PATH=""

while [[ "$1" = --* ]]; do
  OPTION=$1; shift
  case $OPTION in
    (--input_mutants_file)
      INPUT_MUTANTS_FILE=$1;
      shift;;
    (--input_methods_file)
      INPUT_METHODS_FILE=$1;
      shift;;
    (--input_mutants_dir_path)
      INPUT_MUTANTS_DIR_PATH=$1;
      shift;;
    (--output_data_dir_path)
      OUTPUT_DATA_DIR_PATH=$1;
      shift;;
    (--output_mutants_dir_path)
      OUTPUT_MUTANTS_DIR_PATH=$1;
      shift;;
    (--help)
      echo "$USAGE";
      exit 0;;
    (*)
      die "$USAGE";;
  esac
done

# Check whether all arguments have been initialized
[ "$INPUT_MUTANTS_FILE" != "" ]        || die "[ERROR] Missing --input_mutants_file argument!"
[ "$INPUT_METHODS_FILE" != "" ]       || die "[ERROR] Missing --input_methods_file argument!"
[ "$INPUT_MUTANTS_DIR_PATH" != "" ]     || die "[ERROR] Missing --input_mutants_dir_path argument!"
[ "$OUTPUT_DATA_DIR_PATH" != "" ]       || die "[ERROR] Missing --output_dir_path argument!"
[ "$OUTPUT_MUTANTS_DIR_PATH" != "" ]       || die "[ERROR] Missing --output_dir_path argument!"

# Check whether some arguments have been correctly initialized
[ -s "$INPUT_MUTANTS_FILE" ] || die "[ERROR] $INPUT_MUTANTS_FILE does not exist or it is empty!"
[ -s "$INPUT_METHODS_FILE" ] || die "[ERROR] $INPUT_METHODS_FILE does not exist or it is empty!"

# ------------------------------------------------------------------------- Main

# Create output directory, if it does not exist
mkdir -p "$OUTPUT_DATA_DIR_PATH" || die "[ERROR] Failed to create $OUTPUT_DATA_DIR_PATH!"
mkdir -p "$OUTPUT_MUTANTS_DIR_PATH" || die "[ERROR] Failed to create $OUTPUT_MUTANTS_DIR_PATH!"

data_file="$OUTPUT_DATA_DIR_PATH/mut-data-filtered.csv"
echo "benchmark_name,program_name,mutation_position,mutation_operator,mutation,status,parsing_time,plugin_time,resolution_time,verification_time,mut_time,num_pre,num_post" > $data_file || die "[ERROR] Failed to create $OUTPUT_DIR_PATH/$data_file!"
tail -n +2 $INPUT_MUTANTS_FILE | while read -r mutant; do
    benchmark_name=$(echo "$mutant" | cut -d',' -f1 | tr -d '"')
    program_name=$(echo "$mutant" | cut -d',' -f2 | tr -d '"')
    mutation_position=$(echo "$mutant" | cut -d',' -f3 | tr -d '"')
    mutation_operator=$(echo "$mutant" | cut -d',' -f4 | tr -d '"')
    mutation=$(echo "$mutant" | cut -d',' -f5 | tr -d '"')
    status=$(echo "$mutant" | cut -d',' -f6 | tr -d '"')

    num_pre="-"
    num_post="-"
    while read -r method; do
        method_start_pos=$(echo "$method" | cut -d',' -f4 | tr -d '"')
        method_end_pos=$(echo "$method" | cut -d',' -f5 | tr -d '"')

        if [[ "$mutation_position" =~ ^[0-9]+$ ]]; then
            if [[ $mutation_position -ge $method_start_pos ]] && [[ $mutation_position -le $method_end_pos ]]; then
                num_pre=$(echo "$method" | cut -d',' -f6 | tr -d '"')
                num_post=$(echo "$method" | cut -d',' -f7 | tr -d '"')
            fi
        elif [[ "$mutation_position" =~ ^[0-9]+-[0-9]+$ ]]; then
            mutation_start_pos=$(echo "$mutation_position" | cut -d'-' -f1)
            mutation_end_pos=$(echo "$mutation_position" | cut -d'-' -f2)
            if [[ $mutation_start_pos -ge $method_start_pos ]] && [[ $mutation_end_pos -le $method_end_pos ]]; then
                num_pre=$(echo "$method" | cut -d',' -f6 | tr -d '"')
                num_post=$(echo "$method" | cut -d',' -f7 | tr -d '"')
            fi
        fi
    done < <(grep "$benchmark_name,$program_name" "$INPUT_METHODS_FILE")

    if [[ $status = "survived" ]] && [[ ! "$num_post" =~ ^0$ ]]; then
        mutant_dir_path=$INPUT_MUTANTS_DIR_PATH/$mutation_operator/$benchmark_name/$program_name/
        name=$(basename $program_name)
        mutant_file="${name}_${mutation_position}_${mutation_operator}${mutation:+_$mutation}.dfy"
        cp "${mutant_dir_path}/${mutant_file}" $OUTPUT_MUTANTS_DIR_PATH
    fi
    
    echo "$mutant,$num_pre,$num_post" >> "$data_file"
done
