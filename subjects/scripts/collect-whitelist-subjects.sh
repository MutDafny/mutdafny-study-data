#!/usr/bin/env bash
#
# ------------------------------------------------------------------------------
# This script assesses whether the verification of a given set of Dafny programs
# (i.e., .dfy files) runs successfully.
#
# Usage:
# collect-whitelist-subjects.sh
#   [--input_file_path <path, e.g., $SCRIPT_DIR/../data/generated/subjects.csv (by default)>]
#   [--output_file_path <path, e.g., $SCRIPT_DIR/../data/generated/subjects-whitelist.csv (by default)>]
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
  [--input_file_path <path, e.g., $SCRIPT_DIR/../data/generated/subjects.csv (by default)>] \
  [--output_file_path <path, e.g., $SCRIPT_DIR/../data/generated/subjects-whitelist.csv (by default)>] \
  [help]"
if [ "$#" -ne "0" ] && [ "$#" -ne "1" ] && [ "$#" -ne "2" ] && [ "$#" -ne "4" ]; then
  die "$USAGE"
fi

# Print out script's arguments (which could help any debug session)
echo "[INFO] ${BASH_SOURCE[0]} $@"

INPUT_FILE_PATH=""
OUTPUT_FILE_PATH=""

while [[ "$1" = --* ]]; do
  OPTION=$1; shift
  case $OPTION in
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
[ "$INPUT_FILE_PATH" != "" ]  || die "[ERROR] Missing --input_file_path argument!"
[ "$OUTPUT_FILE_PATH" != "" ] || die "[ERROR] Missing --output_file_path argument!"

# Check whether some arguments have been correctly initialized
[ -s "$INPUT_FILE_PATH" ] || die "[ERROR] $INPUT_FILE_PATH does not exist or it is empty!"

# ------------------------------------------------------------------------- Main

# Create output file
echo "benchmark_name,program_name" > "$OUTPUT_FILE_PATH"

tmp_log_file="/tmp/collect-whitelist-subjects-verify-$$.log"
rm -f "$tmp_log_file"

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

  "$DOTNET_HOME_DIR/dotnet" "$MUTDAFNY_HOME_DIR/dafny/Binaries/Dafny.dll" verify "$program_under_test_file_path" \
    --allow-warnings --solver-path "$MUTDAFNY_HOME_DIR/dafny/Binaries/z3" > "$tmp_log_file" 2>&1
  ret="$?"
  cat "$tmp_log_file"

  if [ "$ret" -ne "0" ]; then
    echo "[ERROR] Failed to verify $program_under_test_file_path!"
  elif grep -Eq "^Dafny program verifier finished with 0 verified, 0 errors$" "$tmp_log_file"; then
    echo "[DEBUG] Nothing has been verified!"
  else
    echo "$ben,$pid" >> "$OUTPUT_FILE_PATH"
  fi
done < <(tail -n +2 "$INPUT_FILE_PATH")

# Clean up
rm -f "$tmp_log_file"

echo "DONE!"
exit 0

# EOF
