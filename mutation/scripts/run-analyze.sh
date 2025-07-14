#!/usr/bin/env bash
#
# ------------------------------------------------------------------------------
# Given a Dafny program (i.e., a .dfy file), this script
# stores the methods and functions declared in the file along with their position 
# and the number of pre and postconditions in them, in a nutshell, it runs MutDafny's
# analyze command and writes to the provided output directory one file
# the analyze command and writes to the provided output directory three files
# - `elapsed-time.csv` which reports
#   * parsing time
#   * plugin time
#   * resolution time
#   * verification time
# - `methods.csv` which reports
#   * method name
#   * start token position
#   * end token position
#   * number of preconditions
#   * number of postconditions
#
# Usage:
# run-analyze.sh
#   [--benchmark_name <name of the benchmark, e.g., DafnyBench (by default)>]
#   --input_file_path <full path to a Dafny program, e.g., $SCRIPT_DIR/../../.third-parties/dafnybench/DafnyBench/dataset/ground_truth/630-dafny_tmp_tmpz2kokaiq_Solution.dfy>
#   --output_dir_path <full path, e.g., $SCRIPT_DIR/../data/generated/analyze/data/<Benchmark name, e.g., DafnyBench>/<Dafny program name, e.g., 630-dafny_tmp_tmpz2kokaiq_Solution>/>
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

# ------------------------------------------------------------------------- Args

USAGE="Usage: ${BASH_SOURCE[0]} \
  [--benchmark_name <name of the benchmark, e.g., DafnyBench (by default)>] \
  --input_file_path <full path to a Dafny program, e.g., $SCRIPT_DIR/../../.third-parties/dafnybench/DafnyBench/dataset/ground_truth/630-dafny_tmp_tmpz2kokaiq_Solution.dfy>
  --output_dir_path <full path, e.g., $SCRIPT_DIR/../data/generated/analyze/data/<Benchmark name, e.g., DafnyBench>/<Dafny program name, e.g., 630-dafny_tmp_tmpz2kokaiq_Solution>/>
  [help]"
if [ "$#" -ne "1" ] && [ "$#" -ne "4" ] && [ "$#" -ne "6" ]; then
  die "$USAGE"
fi

# Print out script's arguments (which could help any debug session)
echo "[INFO] ${BASH_SOURCE[0]} $@"

BENCHMARK_NAME="DafnyBench"
INPUT_FILE_PATH=""
OUTPUT_DIR_PATH=""

while [[ "$1" = --* ]]; do
  OPTION=$1; shift
  case $OPTION in
    (--benchmark_name)
      BENCHMARK_NAME=$1;
      shift;;
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
[ "$BENCHMARK_NAME" != "" ]        || die "[ERROR] Missing --benchmark_name argument!"
[ "$INPUT_FILE_PATH" != "" ]       || die "[ERROR] Missing --input_file_path argument!"
[ "$OUTPUT_DIR_PATH" != "" ]       || die "[ERROR] Missing --output_dir_path argument!"

# Check whether some arguments have been correctly initialized
[ -s "$INPUT_FILE_PATH" ] || die "[ERROR] $INPUT_FILE_PATH does not exist or it is empty!"

# ------------------------------------------------------------------------- Main

echo "[INFO] Job started at $(date)"
echo "[INFO] PID: $$"
echo "[INFO] $(hostname)"
echo "[INFO] Running MutDafny's analyze command on $INPUT_FILE_PATH"

# Create output directory, if it does not exist
mkdir -p "$OUTPUT_DIR_PATH" || die "[ERROR] Failed to create $OUTPUT_DIR_PATH!"

# Clean up output directory
rm -rf "$OUTPUT_DIR_PATH"/* "$OUTPUT_DIR_PATH"/.* > /dev/null 2>&1

# Temporary log file
tmp_log_file="/tmp/run-analyze-$$.log"
rm -f "$tmp_log_file"

pushd . > /dev/null 2>&1
cd "$OUTPUT_DIR_PATH"

  start=0
  end=0
  if [ "$BENCHMARK_NAME" == "AWS" ]; then
    start=$(date +%s%3N)
    "$DOTNET_HOME_DIR/dotnet" "$MUTDAFNY_HOME_DIR/dafny/Binaries/Dafny.dll" verify "$INPUT_FILE_PATH" \
      --allow-warnings --solver-path "$MUTDAFNY_HOME_DIR/dafny/Binaries/z3" --function-syntax:3 \
      --plugin "$MUTDAFNY_HOME_DIR/mutdafny/bin/Debug/net8.0/mutdafny.dll,analyze" > "$tmp_log_file" 2>&1
    end=$(date +%s%3N)
  else
    start=$(date +%s%3N)
    "$DOTNET_HOME_DIR/dotnet" "$MUTDAFNY_HOME_DIR/dafny/Binaries/Dafny.dll" verify "$INPUT_FILE_PATH" \
      --allow-warnings --solver-path "$MUTDAFNY_HOME_DIR/dafny/Binaries/z3" \
      --plugin "$MUTDAFNY_HOME_DIR/mutdafny/bin/Debug/net8.0/mutdafny.dll,analyze" > "$tmp_log_file" 2>&1
    end=$(date +%s%3N)
  fi
  cat "$tmp_log_file"

  methods_file="methods.csv"
  if [ -s "$methods_file" ]; then
    echo "[DEBUG] methods_file:"
    cat "$methods_file"
  else
    echo "[DEBUG] $methods_file does not exist or it is empty!"
  fi

  if [ "$BENCHMARK_NAME" == "AWS" ]; then
    program_name=$(echo $INPUT_FILE_PATH | sed "s|.dfy$||g" | sed "s|.*/aws/||")
  elif [ "$BENCHMARK_NAME" == "Consensys" ]; then
    program_name=$(echo $INPUT_FILE_PATH | sed "s|.dfy$||g" | sed "s|.*/consensys/||")
  else
    program_name=$(basename "$INPUT_FILE_PATH" .dfy)
  fi

  data_file="data.csv"
  echo "benchmark_name,program_name,method_name,start_pos,end_pos,num_pre,num_post" > "$data_file" || die "[ERROR] Failed to create $OUTPUT_DIR_PATH/$data_file!"
  tail -n +2 "$methods_file" | while IFS= read -r line; do
    echo "$BENCHMARK_NAME,$program_name,$line"
  done > "$data_file"
  [ -s "$data_file" ] || die "[ERROR] $OUTPUT_DIR_PATH/$data_file does not exist or it is empty!"

  elapsed_time_file="elapsed-time.csv"
  rm -f "$elapsed_time_file"
popd > /dev/null 2>&1

# Clean up
rm -f "$tmp_log_file"

echo "[INFO] Job finished at $(date)"
echo "DONE!"
exit 0

# EOF
