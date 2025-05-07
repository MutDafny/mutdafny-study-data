#!/usr/bin/env bash
#
# ------------------------------------------------------------------------------
# This script downloads and sets up the following tools:
#   - [.Net v9](https://dotnet.microsoft.com/en-us)
#   - [Dafny (5f76b7dba6ccf10ba3c97c690973e8c2fd89efe2)](https://github.com/isabel-amaral/dafny)
#   - [DafnyBench (0cd28feed9cd0179b07fdb9d002f8c39063658e4)](https://github.com/sun-wendy/DafnyBench)
#
# Usage:
#   get-third-parties.sh
#
# ------------------------------------------------------------------------------

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" > /dev/null 2>&1 && pwd)"
source "$SCRIPT_DIR/../utils/scripts/utils.sh" || exit 1

SUBJECTS_FILE="$SCRIPT_DIR/../subjects/data/generated/subjects.csv"
echo "benchmark_name,project_name" > "$SUBJECTS_FILE" || die "[ERROR] Failed to create $SUBJECTS_FILE!"

# ------------------------------------------------------------------------- Deps

# Check whether 'wget' is available
wget --version > /dev/null 2>&1 || die "[ERROR] Could not find 'wget' to download all dependencies. Please install 'wget' and re-run the script."

# Check whether 'git' is available
git --version > /dev/null 2>&1 || die "[ERROR] Could not find 'git' to clone git repositories. Please install 'git' and re-run the script."

# Check whether parallel is available
parallel --version > /dev/null 2>&1 || die "[ERROR] Could not find 'parallel' to run experiments/scripts in parallel. Please install 'GNU Parallel' and re-run the script."

# Check whether 'Rscript' is available
Rscript --version > /dev/null 2>&1 || die "[ERROR] Could not find 'Rscript' to perform, e.g., statistical analysis. Please install 'Rscript' and re-run the script."

# ------------------------------------------------------------------------- Main

OS_NAME=$(uname -s | tr "[:upper:]" "[:lower:]")
OS_ARCH=$(uname -m | tr "[:upper:]" "[:lower:]")

[[ $OS_NAME == *"linux"* ]] || die "[ERROR] All scripts have been developed and tested on Linux, and as we are not sure they will work on other OS, we can continue running this script."

#
# Get and install .Net
#

echo ""
echo "Get and set .Net..."

DOTNET_HOME_DIR="$SCRIPT_DIR/dotnet"
DOTNET_VERSION="9.0.203"
DOTNET_FILE="dotnet-sdk-$DOTNET_VERSION-linux-x64.tar.gz"
DOTNET_URL="https://builds.dotnet.microsoft.com/dotnet/Sdk/$DOTNET_VERSION/$DOTNET_FILE"

# Remove any previous file or directory
rm -rf "$SCRIPT_DIR/$DOTNET_FILE" "$DOTNET_HOME_DIR"

# Get distribution file
wget -np -nv "$DOTNET_URL" -O "$SCRIPT_DIR/$DOTNET_FILE"
if [ "$?" -ne "0" ] || [ ! -s "$SCRIPT_DIR/$DOTNET_FILE" ]; then
  die "[ERROR] Failed to download $DOTNET_URL!"
fi

# Extract it
tar -xvzf "$DOTNET_FILE" -C "$DOTNET_HOME_DIR" || die "[ERROR] Failed to extract $SCRIPT_DIR/$DOTNET_FILE!"
[ -d "$DOTNET_HOME_DIR" ] || die "[ERROR] $DOTNET_HOME_DIR does not exist!"

# Sanity check
# TODO

#
# Get Dafny
#

echo ""
echo "Setting up Dafny..."

DAFNY_HOME_DIR="$SCRIPT_DIR/dafny"

# Remove any previous directory
rm -rf "$DAFNY_HOME_DIR"

git clone https://github.com/isabel-amaral/dafny.git "$DAFNY_HOME_DIR"
if [ "$?" -ne "0" ] || [ ! -d "$DAFNY_HOME_DIR" ]; then
  die "[ERROR] Failed to clone Dafny's repository!"
fi

pushd . > /dev/null 2>&1
cd "$DAFNY_HOME_DIR"
  # Switch to writeable-ast-fields
  git checkout writeable-ast-fields || die "[ERROR] Failed to checkout writeable-ast-fields branch!"
  # Switch to 5f76b7dba6ccf10ba3c97c690973e8c2fd89efe2
  git checkout 5f76b7dba6ccf10ba3c97c690973e8c2fd89efe2 || die "[ERROR] Failed to checkout 5f76b7dba6ccf10ba3c97c690973e8c2fd89efe2!"
popd > /dev/null 2>&1

# Sanity check
# TODO

#
# Get DafnyBench
#

echo ""
echo "Setting up DafnyBench..."

DAFNYBENCH_HOME_DIR="$SCRIPT_DIR/dafnybench"

# Remove any previous directory
rm -rf "$DAFNYBENCH_HOME_DIR"

git clone https://github.com/sun-wendy/DafnyBench.git "$DAFNYBENCH_HOME_DIR"
if [ "$?" -ne "0" ] || [ ! -d "$DAFNYBENCH_HOME_DIR" ]; then
  die "[ERROR] Failed to clone DafnyBench's repository!"
fi

pushd . > /dev/null 2>&1
cd "$DAFNYBENCH_HOME_DIR"
  # Switch to 0cd28feed9cd0179b07fdb9d002f8c39063658e4
  git checkout 0cd28feed9cd0179b07fdb9d002f8c39063658e4 || die "[ERROR] Failed to checkout 0cd28feed9cd0179b07fdb9d002f8c39063658e4!"
popd > /dev/null 2>&1

# Collect set of programs
find "$DAFNYBENCH_HOME_DIR/DafnyBench/dataset/ground_truth" -mindepth 1 -maxdepth 1 -type f -name "*.dfy" -exec basename {} \; | \
  sort --ignore-case | \
  sed "s|.dfy$||g"   | \
  sed "s|^|DafnyBench,|g" >> "$SUBJECTS_FILE"

#
# R packages
#

echo ""
echo "Setting up R..."

Rscript "$SCRIPT_DIR/get-libraries.R" "$SCRIPT_DIR" || die "[ERROR] Failed to install/load all required R packages!"

echo ""
echo "DONE! All third parties have been successfully installed and configured."

# EOF
