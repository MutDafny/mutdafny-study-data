#!/usr/bin/env bash
#
# ------------------------------------------------------------------------------
# This script downloads and sets up the following tools:
#   - [.Net v8.0.111](https://dotnet.microsoft.com/en-us)
#   - [DafnyBench (0cd28feed9cd0179b07fdb9d002f8c39063658e4)](https://github.com/sun-wendy/DafnyBench)
#   - [MutDafny](https://github.com/MutDafny/mutdafny)
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
DOTNET_VERSION="8.0.111"
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
mkdir -p "$DOTNET_HOME_DIR"
tar -xvzf "$DOTNET_FILE" -C "$DOTNET_HOME_DIR" || die "[ERROR] Failed to extract $SCRIPT_DIR/$DOTNET_FILE!"
[ -d "$DOTNET_HOME_DIR" ] || die "[ERROR] $DOTNET_HOME_DIR does not exist!"

# Check whether 'dotnet' is available
export PATH="$DOTNET_HOME_DIR:$PATH"
dotnet --version > /dev/null 2>&1 || die "[ERROR] 'dotnet' is not available!"

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
# Get MutDafny
#

echo ""
echo "Setting up MutDafny..."

MUTDAFNY_HOME_DIR="$SCRIPT_DIR/mutdafny"

# Remove any previous directory
rm -rf "$MUTDAFNY_HOME_DIR"

git clone --recursive https://github.com/MutDafny/mutdafny.git "$MUTDAFNY_HOME_DIR"
if [ "$?" -ne "0" ] || [ ! -d "$MUTDAFNY_HOME_DIR" ]; then
  die "[ERROR] Failed to clone MutDafny's repository!"
fi

pushd . > /dev/null 2>&1
cd "$MUTDAFNY_HOME_DIR"
  # Switch to latest commit/version
  # TODO git checkout ????? || die "[ERROR] Failed to checkout ?????!"

  # Build [Dafny](https://dafny.org)'s submodule
  pushd . > /dev/null 2>&1
  cd dafny   || die "[ERROR] There is no $MUTDAFNY_HOME_DIR/dafny directory!"
    make exe || die "[ERROR] Failed to build Dafny's!"
  popd > /dev/null 2>&1

  # Get [Z3](https://github.com/Z3Prover/z3)
  pushd . > /dev/null 2>&1
  cd dafny/Binaries || die "[ERROR] There is no $MUTDAFNY_HOME_DIR/dafny/Binaries directory!"
    Z3_VERSION="4.12.1"
    Z3_BIN_FILE="$SCRIPT_DIR/z3-$Z3_VERSION"
    Z3_ZIP_FILE="z3-$Z3_VERSION-x64-ubuntu-22.04-bin.zip"
    Z3_URL="https://github.com/dafny-lang/solver-builds/releases/download/snapshot-2024-04-10/$Z3_ZIP_FILE"

    # Remove any previous file or directory
    rm -f "$Z3_BIN_FILE" "$SCRIPT_DIR/$Z3_ZIP_FILE"

    # Get distribution file
    wget -np -nv "$Z3_URL" -O "$SCRIPT_DIR/$Z3_ZIP_FILE"
    if [ "$?" -ne "0" ] || [ ! -s "$SCRIPT_DIR/$Z3_ZIP_FILE" ]; then
      die "[ERROR] Failed to download $Z3_URL!"
    fi

    # Extract it
    unzip "$SCRIPT_DIR/$Z3_ZIP_FILE" || die "[ERROR] Failed to extract $SCRIPT_DIR/$Z3_ZIP_FILE!"
    [ -s "$Z3_BIN_FILE" ] || die "[ERROR] $Z3_BIN_FILE does not exist or it is empty!"

    # Rename it and set its permissions
    mv "$Z3_BIN_FILE" "$SCRIPT_DIR/z3"
    chmod +x "$SCRIPT_DIR/z3"
  pushd . > /dev/null 2>&1

  # Build [MutDafny](https://github.com/MutDafny/mutdafny)
  pushd . > /dev/null 2>&1
  cd mutdafny
    dotnet build || die "[ERROR] Failed to build MutDafny!"
  popd > /dev/null 2>&1
popd > /dev/null 2>&1

# Sanity check
# TODO

#
# R packages
#

echo ""
echo "Setting up R..."

Rscript "$SCRIPT_DIR/get-libraries.R" "$SCRIPT_DIR" || die "[ERROR] Failed to install/load all required R packages!"

echo ""
echo "DONE! All third parties have been successfully installed and configured."

# EOF
