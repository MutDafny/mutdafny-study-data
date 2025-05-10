#!/usr/bin/env bash
#
# ------------------------------------------------------------------------------
# This script creates as many jobs (where each job executes the [`is-verifiable.sh`](is-verifiable.sh)
# script on a Dafny program) as the number of Dafny programs defined in
# [`$SCRIPT_DIR/../data/generated/subjects.csv`]($SCRIPT_DIR/../data/generated/subjects.csv).
#
# Usage:
# gen-is-verifiable-jobs.sh
#   [--input_file_path <path, e.g., $SCRIPT_DIR/../data/generated/subjects.csv (by default)>]
#   [--output_dir_path <path, e.g., $SCRIPT_DIR/../data/generated/is-verifiable (by default)>]
#   [help]
# ------------------------------------------------------------------------------

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" > /dev/null 2>&1 && pwd)"
source "$SCRIPT_DIR/../../utils/scripts/utils.sh" || exit 1

# ------------------------------------------------------------------------- Envs

# Check whether the .third-parties' directory is available
THIRD_PARTIES_DIR="$SCRIPT_DIR/../../.third-parties/"
[ -d "$THIRD_PARTIES_DIR" ] || die "[ERROR] $THIRD_PARTIES_DIR does not exist!"

# Check whether the mutdafny's directory is available
MUTDAFNY_HOME_DIR="$THIRD_PARTIES_DIR/mutdafny"
[ -d "$MUTDAFNY_HOME_DIR" ] || die "[ERROR] $MUTDAFNY_HOME_DIR does not exist!"

# Check whether the dotnet's is available
DOTNET_HOME_DIR="$THIRD_PARTIES_DIR/dotnet"
[ -d "$DOTNET_HOME_DIR" ] || die "[ERROR] $DOTNET_HOME_DIR does not exist!"
"$DOTNET_HOME_DIR/dotnet" --version > /dev/null 2>&1 || die "[ERROR] 'dotnet' is not available!"

# Check whether the dafnybench's directory is available
DAFNYBENCH_HOME_DIR="$THIRD_PARTIES_DIR/dafnybench"
[ -d "$DAFNYBENCH_HOME_DIR" ] || die "[ERROR] $DAFNYBENCH_HOME_DIR does not exist!"

# ------------------------------------------------------------------------- Args

USAGE="Usage: ${BASH_SOURCE[0]} \
  [--input_file_path <path, e.g., $SCRIPT_DIR/../data/generated/subjects.csv (by default)>] \
  [--output_dir_path <path, e.g., $SCRIPT_DIR/../data/generated/is-verifiable (by default)>] \
  [help]"
if [ "$#" -ne "0" ] && [ "$#" -ne "1" ] && [ "$#" -ne "2" ] && [ "$#" -ne "4" ]; then
  die "$USAGE"
fi

# Print out script's arguments (which could help any debug session)
echo "[INFO] ${BASH_SOURCE[0]} $@"

INPUT_FILE_PATH="$SCRIPT_DIR/../data/generated/subjects.csv"
OUTPUT_DIR_PATH="$SCRIPT_DIR/../data/generated/is-verifiable"

while [[ "$1" = --* ]]; do
  OPTION=$1; shift
  case $OPTION in
    (--input_file_path)
      INPUT_FILE_PATH=$1;
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
[ "$INPUT_FILE_PATH" != "" ] || die "[ERROR] Missing --input_file_path argument!"
[ "$OUTPUT_DIR_PATH" != "" ] || die "[ERROR] Missing --output_dir_path argument!"

# Check whether some arguments have been correctly initialized
[ -s "$INPUT_FILE_PATH" ] || die "[ERROR] $INPUT_FILE_PATH does not exist or it is empty!"

# ------------------------------------------------------------------------- Main

# Create output directory, if it does not exist
mkdir -p "$OUTPUT_DIR_PATH" || die "[ERROR] Failed to create $OUTPUT_DIR_PATH!"

# Create experiment's directories
              data_dir_path="$OUTPUT_DIR_PATH/data"
              logs_dir_path="$OUTPUT_DIR_PATH/logs"
              jobs_dir_path="$OUTPUT_DIR_PATH/jobs"
master_job_script_file_path="$SCRIPT_DIR/is-verifiable.sh"
[ -s "$master_job_script_file_path" ] || die "[ERROR] $master_job_script_file_path does not exist or it is empty!"
mkdir -p "$data_dir_path" "$logs_dir_path" "$jobs_dir_path"

# Create set of jobs
while read -r row; do # benchmark_name,program_name
  ben=$(echo "$row" | cut -f1 -d',')
  pid=$(echo "$row" | cut -f2 -d',')
  echo "[DEBUG] $ben :: $pid"

  if [ "$ben" == "DafnyBench" ]; then
    program_under_test_file_path="$DAFNYBENCH_HOME_DIR/DafnyBench/dataset/ground_truth/$pid.dfy"
  else
    die "[ERROR] $ben not supported!"
  fi
  [ -s "$program_under_test_file_path" ] || die "[ERROR] $program_under_test_file_path does not exist or it is empty!"

     job_data_dir_path="$data_dir_path/$pid"
      job_log_dir_path="$logs_dir_path/$pid"
     job_log_file_path="$job_log_dir_path/job.log"
   job_script_dir_path="$jobs_dir_path/$pid"
  job_script_file_path="$job_script_dir_path/job.sh"

  mkdir -p "$job_data_dir_path" "$job_log_dir_path" "$job_script_dir_path"
  touch "$job_log_file_path" "$job_script_file_path"

  echo "#!/usr/bin/env bash" > "$job_script_file_path"
  echo "#"                  >> "$job_script_file_path"
  echo "# timefactor:1"     >> "$job_script_file_path"
  echo "bash $master_job_script_file_path \
  --benchmark_name \"$ben\" \
  --input_file_path \"$program_under_test_file_path\" \
  --output_file_path \"$job_data_dir_path\" > \"$job_log_file_path\" 2>&1" >> "$job_script_file_path"
done < <(tail -n +2 "$INPUT_FILE_PATH")

echo "Jobs have been created. Please run the $SCRIPT_DIR/../../utils/scripts/run-jobs.sh script on the generated jobs, e.g., $SCRIPT_DIR/../../utils/scripts/run-jobs.sh --jobs_dir_path $OUTPUT_DIR_PATH/jobs."

echo "DONE!"
exit 0

# EOF
