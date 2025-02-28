#!/bin/bash

DIR=$(cd "$(dirname "$0")" && pwd)
cd "$DIR" &> /dev/null
rm commits.csv
touch commits.csv

scraped_repos=0
fix_commits=0
correct_commits=0
update_commits=0
change_commits=0


extract_commits_matching_pattern() {
    local pattern=$1
    local repo_url=$2
    local -n count_ref=$3

    echo "Extracting commits containing $pattern"
    readarray -t commits < <(git log | grep -i -B 4 $pattern | grep ^commit.*)
    for commit in "${commits[@]}"
    do
        hash=$(echo $commit | sed 's/commit //g')
        dafny_files=$(git show --name-only $hash | grep .dfy&)
        if [[ -n $dafny_files ]]; then # only save commits that change dafny files
            commit_url="${repo_url}/commit/${hash}"
            echo $commit_url >> ../commits.csv
            count_ref=$((count_ref + 1))
        fi
    done
}


readarray -t repos < repos.txt

for repo_url in "${repos[@]}"
do
    repo_url=$(echo $repo_url | sed -e 's/\r$//')
    echo Cloning $repo_url
    git clone $repo_url
    repo_name=$(basename $repo_url)
    cd $repo_name

    extract_commits_matching_pattern "fix" $repo_url fix_commits
    extract_commits_matching_pattern "correct" $repo_url correct_commits
    extract_commits_matching_pattern "updat" $repo_url update_commits
    extract_commits_matching_pattern "chang" $repo_url change_commits
    scraped_repos=$((scraped_repos + 1))
    echo $scraped_repos / 110 extracted

    cd ..
    echo Removing $repo_name
    rm -rf $repo_name
    echo
done

shuffled=$(shuf commits.csv)
echo "$shuffled" > commits.csv

echo Extracted $fix_commits commits containing fix
echo Extracted $correct_commits commits containing correct
echo Extracted $update_commits commits containing updat
echo Extracted $change_commits commits containing chang

cd - &> /dev/null