#!/usr/bin/env bash
#
# ------------------------------------------------------------------------------
# This script creates as many jobs (where each job executes the [`run-mut.sh`](run-mut.sh)
# script on a Dafny program and a mutation operator) as the number of Dafny programs
# defined in [`$SCRIPT_DIR/../../subjects/data/generated/subjects-whitelist.csv`]($SCRIPT_DIR/../../subjects/data/generated/subjects-whitelist.csv)
# times the number of mutation operators.
#
# Usage:
# gen-mut-jobs.sh
#   [--input_file_path <full path, e.g., $SCRIPT_DIR/../../subjects/data/generated/subjects-whitelist.csv (by default)>]
#    --mutation_operators <set of mutation operator(s) one or more, separated by ',', possible values AOR|ROR|COR|LOR|SOR|BBR|AOI|COI|LOI|AOD|COD|LOD|LVR|EVR|VER|LSR|LBI|MRR|MAP|MNR|MCR|MVR|SAR|CIR|CBR|CBE|TAR|DCR|SDL|VDL|SLD|ODL|THI|THD|AMR|MMR|FAR|PRV|SWS|SWV>
#    --scan_dir_path <full path, e.g., $SCRIPT_DIR/../data/generated/scan>
#   [--output_dir_path <full path, e.g., $SCRIPT_DIR/../data/generated/mut (by default)>]
#   [help]
# ------------------------------------------------------------------------------

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" > /dev/null 2>&1 && pwd)"
source "$SCRIPT_DIR/../../utils/scripts/utils.sh" || exit 1

# -------------------------------------------------------------------------- Env

# Check whether the .third-parties' directory is available
THIRD_PARTIES_DIR="$SCRIPT_DIR/../../.third-parties/"
[ -d "$THIRD_PARTIES_DIR" ] || die "[ERROR] $THIRD_PARTIES_DIR does not exist!"

# Check whether the mutdafny's directory is available
MUTDAFNY_HOME_DIR="$THIRD_PARTIES_DIR/mutdafny"
[ -d "$MUTDAFNY_HOME_DIR" ] || die "[ERROR] $MUTDAFNY_HOME_DIR does not exist!"

# Check whether the dafnybench's, aws's and consensys's directories are available
DAFNYBENCH_HOME_DIR="$THIRD_PARTIES_DIR/dafnybench"
[ -d "$DAFNYBENCH_HOME_DIR" ] || die "[ERROR] $DAFNYBENCH_HOME_DIR does not exist!"
AWS_HOME_DIR="$THIRD_PARTIES_DIR/aws"
[ -d "$AWS_HOME_DIR" ] || die "[ERROR] $AWS_HOME_DIR does not exist!"
CONSENSYS_HOME_DIR="$THIRD_PARTIES_DIR/consensys"
[ -d "$CONSENSYS_HOME_DIR" ] || die "[ERROR] $CONSENSYS_HOME_DIR does not exist!"

# ------------------------------------------------------------------------- Args

USAGE="Usage: ${BASH_SOURCE[0]} \
  [--input_file_path <full path, e.g., $SCRIPT_DIR/../../subjects/data/generated/subjects-whitelist.csv (by default)>] \
   --mutation_operators <set of mutation operator(s) one or more, separated by ',', possible values AOR|ROR|COR|LOR|SOR|BBR|AOI|COI|LOI|AOD|COD|LOD|LVR|EVR|VER|LSR|LBI|MRR|MAP|MNR|MCR|MVR|SAR|CIR|CBR|CBE|TAR|DCR|SDL|VDL|SLD|ODL|THI|THD|AMR|MMR|FAR|PRV|SWS|SWV> \
   --scan_dir_path <full path, e.g., $SCRIPT_DIR/../data/generated/scan> \
  [--output_dir_path <full path, e.g., $SCRIPT_DIR/../data/generated/mut (by default)>] \
  [help]"
if [ "$#" -ne "1" ] && [ "$#" -ne "4" ] && [ "$#" -ne "6" ] && [ "$#" -ne "8" ]; then
  die "$USAGE"
fi

# Print out script's arguments (which could help any debug session)
echo "[INFO] ${BASH_SOURCE[0]} $@"

INPUT_FILE_PATH="$SCRIPT_DIR/../../subjects/data/generated/subjects-whitelist.csv"
MUTATION_OPERATORS=""
SCAN_DIR_PATH="$SCRIPT_DIR/../data/generated/scan"
OUTPUT_DIR_PATH="$SCRIPT_DIR/../data/generated/mut"

while [[ "$1" = --* ]]; do
  OPTION=$1; shift
  case $OPTION in
    (--input_file_path)
      INPUT_FILE_PATH=$1;
      shift;;
    (--mutation_operators)
      MUTATION_OPERATORS=$1;
      shift;;
    (--scan_dir_path)
      SCAN_DIR_PATH=$1;
      shift;;
    (--output_dir_path)
      OUTPUT_DIR_PATH=$1;
      shift;;
    (--help)
      echo "$USAGE";
      exit 0;;
    (*)
      die "$USAGE";;
  esac
done

# Check whether all arguments have been initialized
[ "$INPUT_FILE_PATH" != "" ]    || die "[ERROR] Missing --input_file_path argument!"
[ "$MUTATION_OPERATORS" != "" ] || die "[ERROR] Missing --mutation_operators argument!"
[ "$SCAN_DIR_PATH" != "" ]      || die "[ERROR] Missing --scan_dir_path argument!"
[ "$OUTPUT_DIR_PATH" != "" ]    || die "[ERROR] Missing --output_dir_path argument!"

# Check whether input files exist and it is not empty
[ -s "$INPUT_FILE_PATH" ] || die "[ERROR] $INPUT_FILE_PATH does not exist or it is empty!"
[ -d "$SCAN_DIR_PATH" ]   || die "[ERROR] $SCAN_DIR_PATH does not exist!"

# ------------------------------------------------------------------------- Args

# Create output directory, if it does not exist
mkdir -p "$OUTPUT_DIR_PATH" || die "[ERROR] Failed to create $OUTPUT_DIR_PATH!"

# Create experiment's directories
              data_dir_path="$OUTPUT_DIR_PATH/data"
           mutants_dir_path="$OUTPUT_DIR_PATH/mutants"
              logs_dir_path="$OUTPUT_DIR_PATH/logs"
              jobs_dir_path="$OUTPUT_DIR_PATH/jobs"
master_job_script_file_path="$SCRIPT_DIR/run-mut.sh"
[ -s "$master_job_script_file_path" ] || die "[ERROR] $master_job_script_file_path does not exist or it is empty!"
mkdir -p "$data_dir_path" "$mutants_dir_path" "$logs_dir_path" "$jobs_dir_path"

# Create set of jobs
while read -r row; do # benchmark_name,program_name
  ben=$(echo "$row" | cut -f1 -d',')
  pid=$(echo "$row" | cut -f2 -d',')
  echo "[DEBUG] $ben :: $pid"

  if [ "$ben" == "DafnyBench" ]; then
    program_under_test_file_path="$DAFNYBENCH_HOME_DIR/DafnyBench/dataset/ground_truth/$pid.dfy"
  elif [ "$ben" == "AWS" ]; then
    program_under_test_file_path="$AWS_HOME_DIR/$pid.dfy"
  elif [ "$ben" == "Consensys" ]; then
    program_under_test_file_path="$CONSENSYS_HOME_DIR/$pid.dfy"
  else
    die "[ERROR] $ben not supported!"
  fi
  [ -s "$program_under_test_file_path" ] || die "[ERROR] $program_under_test_file_path does not exist or it is empty!"

  for op in $(echo "$MUTATION_OPERATORS" | tr ',' '\n'); do
    echo "[DEBUG] $ben :: $pid :: $op"

    targets_file="$SCAN_DIR_PATH/data/$op/$ben/$pid/targets.csv"
    [ -s "$targets_file" ] || continue # Skip execution if there is nothing to mutate

       job_data_dir_path="$data_dir_path/$op/$ben/$pid"
    job_mutants_dir_path="$mutants_dir_path/$op/$ben/$pid"
        job_log_dir_path="$logs_dir_path/$op/$ben/$pid"
       job_log_file_path="$job_log_dir_path/job.log"
     job_script_dir_path="$jobs_dir_path/$op/$ben/$pid"
    job_script_file_path="$job_script_dir_path/job.sh"

    mkdir -p "$job_data_dir_path" "$job_mutants_dir_path" "$job_log_dir_path" "$job_script_dir_path"
    touch "$job_log_file_path" "$job_script_file_path"

    echo "#!/usr/bin/env bash" > "$job_script_file_path"
    echo "#"                  >> "$job_script_file_path"
    echo "# timefactor:1"     >> "$job_script_file_path"
    echo "bash $master_job_script_file_path \
  --benchmark_name \"$ben\" \
  --input_file_path \"$program_under_test_file_path\" \
  --targets_file_path \"$targets_file\" \
  --output_file_path \"$job_data_dir_path/data.csv\" \
  --output_dir_path \"$job_mutants_dir_path\" > \"$job_log_file_path\" 2>&1" >> "$job_script_file_path"
  done
done < <(tail -n +2 "$INPUT_FILE_PATH")

echo "Jobs have been created. Please run the $SCRIPT_DIR/../../utils/scripts/run-jobs.sh script on the generated jobs, e.g., $SCRIPT_DIR/../../utils/scripts/run-jobs.sh --jobs_dir_path $OUTPUT_DIR_PATH/jobs."

echo "DONE!"
exit 0

# EOF
