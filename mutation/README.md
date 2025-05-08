# Mutation

<!-- TBA -->

## Scripts

- [`scripts/run-scan.sh`](scripts/run-scan.sh) runs given a Dafny program (i.e., a .dfy file) and a mutation operator, this script generates the set of target locations to mutate, in a nutshell, it runs MutDafny's scan command.

Usage example:

```bash
bash scripts/run-scan.sh \
  --input_file_path ../.third-parties/dafnybench/DafnyBench/dataset/ground_truth/630-dafny_tmp_tmpz2kokaiq_Solution.dfy \
  --mutation_operator BOR \
  --output_directory_path data/generated/scan/stats/BOR/dafny_tmp_tmpz2kokaiq_Solution/
```

**Note:** The script [`scripts/gen-scan-jobs.sh`](scripts/gen-scan-jobs.sh) automatizes the process of running MutDafny's scan command on **all** programs listed in [`../subjects/data/generated/subjects.csv`](../subjects/data/generated/subjects.csv) on one or more mutation operators.

## Data

<!-- TBA -->

## Statistics

<!-- TBA -->
