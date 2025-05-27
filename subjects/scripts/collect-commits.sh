#!/usr/bin/env bash
#
# ------------------------------------------------------------------------------
# Given a set of GitHub URLs, this script collects the commits in each repository
# that match specific keywords (e.g., fix) and writes to the provided file the
# following metadata:
# - The URL of a commit message that match specific keywords (e.g., fix)
# - Number of .dfy modified, removed, or added in the commit
# - Number of insertions in the commit
# - Number of deletions in the commit
#
# Usage:
# collect-commits.sh
#   [--repositories_file_path <full path, e.g., $SCRIPT_DIR/../data/generated/repositories.csv (by default)>]
#   [--output_file_path <full path, e.g., $SCRIPT_DIR/../data/generated/commits.csv (by default)>]
#   [help]
# ------------------------------------------------------------------------------

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" > /dev/null 2>&1 && pwd)"
source "$SCRIPT_DIR/../../utils/scripts/utils.sh" || exit 1

# ------------------------------------------------------------------------- Args

USAGE="Usage: ${BASH_SOURCE[0]} \
  [--repositories_file_path <full path, e.g., $SCRIPT_DIR/../data/generated/repositories.csv (by default)>] \
  [--output_file_path <full path, e.g., $SCRIPT_DIR/../data/generated/commits.csv (by default)>] \
  [help]"
if [ "$#" -ne "0" ] && [ "$#" -ne "1" ] && [ "$#" -ne "2" ] && [ "$#" -ne "4" ]; then
  die "$USAGE"
fi

# Print out script's arguments (which could help any debug session)
echo "[INFO] ${BASH_SOURCE[0]} $@"

REPOSITORIES_FILE_PATH="$SCRIPT_DIR/../data/generated/repositories.csv"
OUTPUT_FILE_PATH="$SCRIPT_DIR/../data/generated/commits.csv"

while [[ "$1" = --* ]]; do
  OPTION=$1; shift
  case $OPTION in
    (--repositories_file_path)
      REPOSITORIES_FILE_PATH=$1;
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
[ "$REPOSITORIES_FILE_PATH" != "" ] || die "[ERROR] Missing --repositories_file_path argument!"
[ "$OUTPUT_FILE_PATH" != "" ]       || die "[ERROR] Missing --output_file_path argument!"

# Check whether some arguments have been correctly initialized
[ -s "$REPOSITORIES_FILE_PATH" ]    || die "[ERROR] $REPOSITORIES_FILE_PATH does not exist or it is empty!"

# ------------------------------------------------------------------------- Util

extract_commits_matching_pattern() {
  local USAGE="Usage: ${FUNCNAME[0]} <repository_url> <pattern>"
  if [ "$#" -ne "2" ] ; then
    echo "$USAGE" >&2
    return 1
  fi

  # Args
  local repository_url="$1"
  local pattern="$2"

  count=0
  while read -r hash; do
    num_dafny_files_in_the_commit=$(git show --name-only --pretty="" "$hash" | grep ".dfy$" | wc -l)
    [ "$num_dafny_files_in_the_commit" -gt "0" ] || continue # No Dafny file has been modified, removed, or added

    echo "[DEBUG] The commit message of the commit $hash contains '$pattern'" >&2
    commit_url="$repository_url/commit/$hash"
    stats=$(git show --numstat --pretty="" "$hash" | grep ".dfy$" | awk '{ins+=$1; del+=$2} END {print ins "," del}')
    echo "$commit_url,$num_dafny_files_in_the_commit,$stats" >> "$OUTPUT_FILE_PATH"

    count=$((count + 1))
  done < <(git log --all -i --until="2025-03-02" --grep="$pattern" --pretty=format:'%H') # Get all commits hash that contain '$pattern' in the commit message

  echo "$count"
  return 0
}

# ------------------------------------------------------------------------- Main

rm -f "$OUTPUT_FILE_PATH"
echo "commit_url,num_dfy_files,num_insertions,num_deletions" > "$OUTPUT_FILE_PATH" || die "[ERROR] Failed to create $OUTPUT_FILE_PATH!"

# Temporary working directory
WORK_DIR="/tmp/collect-commits-$$"
mkdir -p "$WORK_DIR" || die "[ERROR] Failed to create $WORK_DIR!"

# Counters
num_repositories=$(wc -l < "$REPOSITORIES_FILE_PATH")
fix_commits=0
correct_commits=0
update_commits=0
change_commits=0
num_scraped_repos=0

while read -r repository_url; do
  # Clean up working directory
  rm -rf "$WORK_DIR"/* "$WORK_DIR"/.* > /dev/null 2>&1

  echo "[DEBUG] Cloning $repository_url to $WORK_DIR" >&2
  git clone "$repository_url" "$WORK_DIR" || die "[ERROR] Failed to clone $repository_url to $WORK_DIR!"

  pushd . > /dev/null 2>&1
  cd "$WORK_DIR/"
    fix_commits=$((fix_commits + $(extract_commits_matching_pattern "$repository_url" "fix")))
    correct_commits=$((correct_commits + $(extract_commits_matching_pattern "$repository_url" "correct")))
    update_commits=$((update_commits + $(extract_commits_matching_pattern "$repository_url" "updat")))
    change_commits=$((change_commits + $(extract_commits_matching_pattern "$repository_url" "chang")))
  popd > /dev/null 2>&1

  num_scraped_repos=$((num_scraped_repos + 1))
  echo "[DEBUG] Scraped $num_scraped_repos out of $num_repositories" >&2
done < <(cat "$REPOSITORIES_FILE_PATH")

# Header
head -n1 "$OUTPUT_FILE_PATH" > "$OUTPUT_FILE_PATH.tmp"
# Unique ordered content
tail -n +2 "$OUTPUT_FILE_PATH" | sort --unique --ignore-case >> "$OUTPUT_FILE_PATH.tmp"
# Replace it
mv "$OUTPUT_FILE_PATH.tmp" "$OUTPUT_FILE_PATH"

# Print out some stats
echo "[INFO] Collected $fix_commits commits containing 'fix'"
echo "[INFO] Collected $correct_commits commits containing 'correct'"
echo "[INFO] Collected $update_commits commits containing 'updat'"
echo "[INFO] Collected $change_commits commits containing 'chang'"

# Clean up
rm -rf "$WORK_DIR"

echo "DONE!"
exit 0

# EOF
