#!/usr/bin/env bash

UTILS_SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" > /dev/null 2>&1 && pwd)"
USER_HOME_DIR="$(cd ~ && pwd)"

#
# Print error message to the stdout and exit.
#
die() {
  echo "$@" >&2
  exit 1
}

#
# Given a relative path, this function converts it into a full/absolute path.
#
rel_to_abs_filename() {
  local USAGE="Usage: ${FUNCNAME[0]}"
  if [ "$#" != 1 ] ; then
    echo "$USAGE" >&2
    return 1
  fi

  rel_filename="$1"
  echo "$(cd "$(dirname "$rel_filename")" && pwd)/$(basename "$rel_filename")" || return 1

  return 0
}

#
# Get number of CPUs
#
_get_number_of_cpus() {
  local USAGE="Usage: ${FUNCNAME[0]}"
  if [ "$#" != 0 ] ; then
    echo "$USAGE" >&2
    return 1
  fi

  num_cpus="1" # by default
  dist=$(uname)
  if [ "$dist" == "Darwin" ]; then
    num_cpus=$(sysctl -n hw.ncpu)
  elif [ "$dist" == "Linux" ]; then
    num_cpus=$(cat /proc/cpuinfo | grep 'cpu cores' | sort -u | cut -f2 -d':' | cut -f2 -d' ')
  fi

  echo "$num_cpus"
  return 0
}

#
# Check whether the machine has the software that allows one to run jobs
# in parallel.  Return true ('0') if yes, otherwise it returns false ('1').
#
_can_I_run_jobs_simultaneously() {
  if sbatch --version > /dev/null 2>&1; then
    return 0 # true
  fi
  if man parallel > /dev/null 2>&1; then
    return 0 # true
  fi
  return 1 # false
}

# EOF
