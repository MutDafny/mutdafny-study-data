#!/usr/bin/env bash
#
# ------------------------------------------------------------------------------
# This script assesses whether the verification of a given a Dafny program
# (i.e., a .dfy file) runs successfully.
#
# Usage:
# is-verifiable.sh
#   [--benchmark_name <name of the benchmark, e.g., DafnyBench (by default)>]
#   --input_file_path <full path to a Dafny program, e.g., $SCRIPT_DIR/../../.third-parties/dafnybench/DafnyBench/dataset/ground_truth/630-dafny_tmp_tmpz2kokaiq_Solution.dfy>
#   --output_file_path <path, e.g., $SCRIPT_DIR/../data/generated/is-verifiable/<Benchmark name, e.g., DafnyBench>/<Dafny program name, e.g., 630-dafny_tmp_tmpz2kokaiq_Solution>/data.csv>
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
  --input_file_path <full path to a Dafny program, e.g., $SCRIPT_DIR/../../.third-parties/dafnybench/DafnyBench/dataset/ground_truth/630-dafny_tmp_tmpz2kokaiq_Solution.dfy> \
  --output_file_path <path, e.g., $SCRIPT_DIR/../data/generated/is-verifiable/<Benchmark name, e.g., DafnyBench>/<Dafny program name, e.g., 630-dafny_tmp_tmpz2kokaiq_Solution>/data.csv> \
  [help]"
if [ "$#" -ne "1" ] && [ "$#" -ne "4" ] && [ "$#" -ne "6" ]; then
  die "$USAGE"
fi

# Print out script's arguments (which could help any debug session)
echo "[INFO] ${BASH_SOURCE[0]} $@"

BENCHMARK_NAME="DafnyBench"
INPUT_FILE_PATH=""
OUTPUT_FILE_PATH=""

while [[ "$1" = --* ]]; do
  OPTION=$1; shift
  case $OPTION in
    (--benchmark_name)
      BENCHMARK_NAME=$1;
      shift;;
    (--input_file_path)
      INPUT_FILE_PATH=$1;
      shift;;
    (--output_file_path)
      OUTPUT_FILE_PATH=$1;
      shift;;
    (--help)
      echo "$USAGE";
      exit 0;;
    (*)
      die "$USAGE";;
  esac
done

# Check whether all arguments have been initialized
[ "$BENCHMARK_NAME" != "" ]   || die "[ERROR] Missing --benchmark_name argument!"
[ "$INPUT_FILE_PATH" != "" ]  || die "[ERROR] Missing --input_file_path argument!"
[ "$OUTPUT_FILE_PATH" != "" ] || die "[ERROR] Missing --output_file_path argument!"

# Check whether some arguments have been correctly initialized
[ -s "$INPUT_FILE_PATH" ] || die "[ERROR] $INPUT_FILE_PATH does not exist or it is empty!"

# ------------------------------------------------------------------------- Main

echo "[INFO] Job started at $(date)"
echo "[INFO] PID: $$"
echo "[INFO] $(hostname)"
echo "[INFO] Running Dafny's verify command on $INPUT_FILE_PATH"

# Temporary log file
tmp_log_file="/tmp/is-verifiable-$$.log"
rm -f "$tmp_log_file"

start=$(date +%s%3N)
"$DOTNET_HOME_DIR/dotnet" "$MUTDAFNY_HOME_DIR/dafny/Binaries/Dafny.dll" verify "$INPUT_FILE_PATH" \
  --allow-warnings --solver-path "$MUTDAFNY_HOME_DIR/dafny/Binaries/z3" > "$tmp_log_file" 2>&1
end=$(date +%s%3N)
cat "$tmp_log_file"

if grep -Eq "^Dafny program verifier finished with [1-9]+ verified, 0 errors" "$tmp_log_file"; then
  echo "[DEBUG] $INPUT_FILE_PATH is verifiable"
  is_verifiable=1
else
  echo "[DEBUG] $INPUT_FILE_PATH is not verifiable"
  is_verifiable=0
fi

# Create data file
mkdir -p $(dirname "$OUTPUT_FILE_PATH")
echo "benchmark_name,program_name,is_verifiable,runtime" > "$OUTPUT_FILE_PATH" || die "[ERROR] Failed to create $OUTPUT_FILE_PATH!"
# Populate it
echo "$BENCHMARK_NAME,$(basename "$INPUT_FILE_PATH" .dfy),$is_verifiable,$(echo $end - $start | bc)" >> "$OUTPUT_FILE_PATH"

# Clean up
rm -f "$tmp_log_file"

echo "[INFO] Job finished at $(date)"
echo "DONE!"
exit 0

# EOF
