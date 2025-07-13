#!/usr/bin/env bash
#
# ------------------------------------------------------------------------------
# Given a Dafny program (i.e., a .dfy file) and a mutation operator, this script
# generates the set of target locations to mutate, in a nutshell, it runs MutDafny's
# scan command and writes to the provided output directory three files
# - `elapsed-time.csv` which reports
#   * parsing time
#   * plugin time
#   * resolution time
#   * verification time
# - `targets.csv`
# - `data.csv` which reports
#   * program name
#   * mutation operator
#   * (all data reported by `elapsed-time.csv`)
#   * number of rows in `targets.csv`
#   * scan time as the total time to run MutDafny's scan command
#
# Usage:
# run-scan.sh
#   [--benchmark_name <name of the benchmark, e.g., DafnyBench (by default)>]
#   --input_file_path <full path to a Dafny program, e.g., $SCRIPT_DIR/../../.third-parties/dafnybench/DafnyBench/dataset/ground_truth/630-dafny_tmp_tmpz2kokaiq_Solution.dfy>
#   --mutation_operator <BOR|BBR|UOI|UOD|LVR|EVR|VER|LSR|LBI|MRR|MAP|MNR|MCR|MVR|SAR|CIR|CBR|CBE|TAR|DCR|SDL|VDL|SLD|ODL|THI|THD|AMR|MMR|FAR|PRV|SWS|SWV>
#   --output_dir_path <full path, e.g., $SCRIPT_DIR/../data/generated/scan/data/<mutation operator, e.g., BOR>/<Benchmark name, e.g., DafnyBench>/<Dafny program name, e.g., 630-dafny_tmp_tmpz2kokaiq_Solution>/>
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
  --mutation_operator <BOR|BBR|UOI|UOD|LVR|EVR|VER|LSR|LBI|MRR|MAP|MNR|MCR|MVR|SAR|CIR|CBR|CBE|TAR|DCR|SDL|VDL|SLD|ODL|THI|THD|AMR|MMR|FAR|PRV|SWS|SWV> \
  --output_dir_path <full path, e.g., $SCRIPT_DIR/../data/generated/scan/data/<mutation operator, e.g., BOR>/<Benchmark name, e.g., DafnyBench>/<Dafny program name, e.g., 630-dafny_tmp_tmpz2kokaiq_Solution>/> \
  [help]"
if [ "$#" -ne "1" ] && [ "$#" -ne "6" ] && [ "$#" -ne "8" ]; then
  die "$USAGE"
fi

# Print out script's arguments (which could help any debug session)
echo "[INFO] ${BASH_SOURCE[0]} $@"

BENCHMARK_NAME="DafnyBench"
INPUT_FILE_PATH=""
MUTATION_OPERATOR=""
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
    (--mutation_operator)
      MUTATION_OPERATOR=$1;
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
[ "$MUTATION_OPERATOR" != "" ]     || die "[ERROR] Missing --mutation_operator argument!"
[ "$OUTPUT_DIR_PATH" != "" ]       || die "[ERROR] Missing --output_dir_path argument!"

# Check whether some arguments have been correctly initialized
[ -s "$INPUT_FILE_PATH" ] || die "[ERROR] $INPUT_FILE_PATH does not exist or it is empty!"

# ------------------------------------------------------------------------- Main

echo "[INFO] Job started at $(date)"
echo "[INFO] PID: $$"
echo "[INFO] $(hostname)"
echo "[INFO] Running MutDafny's scan command ($MUTATION_OPERATOR mutation operator) on $INPUT_FILE_PATH"

MUTATION_OPERATOR_ARG="$MUTATION_OPERATOR"
if [ "$MUTATION_OPERATOR" == "ALL" ]; then
  MUTATION_OPERATOR_ARG="BOR BBR UOI UOD LVR EVR VER LSR LBI MRR MAP MNR MCR MVR SAR CIR CBR CBE TAR DCR SDL VDL SLD ODL THI THD AMR MMR FAR PRV SWS SWV"
fi

# Create output directory, if it does not exist
mkdir -p "$OUTPUT_DIR_PATH" || die "[ERROR] Failed to create $OUTPUT_DIR_PATH!"

# Clean up output directory
rm -rf "$OUTPUT_DIR_PATH"/* "$OUTPUT_DIR_PATH"/.* > /dev/null 2>&1

# Temporary log file
tmp_log_file="/tmp/run-scan-$$.log"
rm -f "$tmp_log_file"

pushd . > /dev/null 2>&1
cd "$OUTPUT_DIR_PATH"

  start=0
  end=0
  if [ "$BENCHMARK_NAME" == "AWS" ]; then
    start=$(date +%s%3N)
    "$DOTNET_HOME_DIR/dotnet" "$MUTDAFNY_HOME_DIR/dafny/Binaries/Dafny.dll" verify "$INPUT_FILE_PATH" \
      --allow-warnings --solver-path "$MUTDAFNY_HOME_DIR/dafny/Binaries/z3" --function-syntax:3 \
      --plugin "$MUTDAFNY_HOME_DIR/mutdafny/bin/Debug/net8.0/mutdafny.dll","scan $MUTATION_OPERATOR_ARG" > "$tmp_log_file" 2>&1
    end=$(date +%s%3N)
  else
    start=$(date +%s%3N)
    "$DOTNET_HOME_DIR/dotnet" "$MUTDAFNY_HOME_DIR/dafny/Binaries/Dafny.dll" verify "$INPUT_FILE_PATH" \
      --allow-warnings --solver-path "$MUTDAFNY_HOME_DIR/dafny/Binaries/z3" \
      --plugin "$MUTDAFNY_HOME_DIR/mutdafny/bin/Debug/net8.0/mutdafny.dll","scan $MUTATION_OPERATOR_ARG" > "$tmp_log_file" 2>&1
    end=$(date +%s%3N)
  fi
  cat "$tmp_log_file"

  if ! grep -Eq "^Dafny program verifier finished with [1-9][0-9]* verified, 0 errors" "$tmp_log_file"; then
    die "[ERROR] Failed to run MutDafny's scan command ($MUTATION_OPERATOR mutation operator) on $INPUT_FILE_PATH!"
  fi

  elapsed_time_file="elapsed-time.csv" # parsing_time,plugin_time,resolution_time,verification_time
  [ -s "$elapsed_time_file" ] || die "[ERROR] $elapsed_time_file does not exist or it is empty!"
  echo "[DEBUG] $elapsed_time_file:"
  cat "$elapsed_time_file"

  targets_file="targets.csv"
  if [ -s "$targets_file" ]; then
    echo "[DEBUG] targets_file:"
    cat "$targets_file"
    number_of_targets=$(wc -l < "$targets_file")
  else
    echo "[DEBUG] $targets_file does not exist or it is empty!"
    number_of_targets=0
  fi

  data_file="data.csv"
  echo "benchmark_name,program_name,mutation_operator,parsing_time,plugin_time,resolution_time,verification_time,number_of_targets,scan_time" > "$data_file" || die "[ERROR] Failed to create $OUTPUT_DIR_PATH/$data_file!"
  if [ "$BENCHMARK_NAME" == "AWS" ]; then
    echo "$BENCHMARK_NAME,$(echo $INPUT_FILE_PATH | sed "s|.dfy$||g" | sed "s|.*/aws/||"),$MUTATION_OPERATOR,$(tail -n1 $elapsed_time_file),$number_of_targets,$(echo $end - $start | bc)" >> "$data_file" || die "[ERROR] Failed to populate $OUTPUT_DIR_PATH/$data_file!"
  elif [ "$BENCHMARK_NAME" == "Consensys" ]; then
    echo "$BENCHMARK_NAME,$(echo $INPUT_FILE_PATH | sed "s|.dfy$||g" | sed "s|.*/consensys/||"),$MUTATION_OPERATOR,$(tail -n1 $elapsed_time_file),$number_of_targets,$(echo $end - $start | bc)" >> "$data_file" || die "[ERROR] Failed to populate $OUTPUT_DIR_PATH/$data_file!"
  else
    echo "$BENCHMARK_NAME,$(basename "$INPUT_FILE_PATH" .dfy),$MUTATION_OPERATOR,$(tail -n1 $elapsed_time_file),$number_of_targets,$(echo $end - $start | bc)" >> "$data_file" || die "[ERROR] Failed to populate $OUTPUT_DIR_PATH/$data_file!"
  fi
  [ -s "$data_file" ] || die "[ERROR] $OUTPUT_DIR_PATH/$data_file does not exist or it is empty!"

  rm -f "$elapsed_time_file"
popd > /dev/null 2>&1

# Clean up
rm -f "$tmp_log_file"

echo "[INFO] Job finished at $(date)"
echo "DONE!"
exit 0

# EOF
