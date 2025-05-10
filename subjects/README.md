# Subjects

A total of 785 programs from the [DafnyBench](https://github.com/sun-wendy/DafnyBench) benchmark.

```
@article{loughridge2024dafnybench,
  title = {{DafnyBench: A Benchmark for Formal Software Verification}},
  author = {Chloe Loughridge and Qinyi Sun and Seth Ahrenbach and Federico Cassano and Chuyue Sun and Ying Sheng and Anish Mudide and Md Rakib Hossain Misu and Nada Amin and Max Tegmark},
  year = {2024},
  journal = {arXiv preprint arXiv:2406.08467}
}
```

## Scripts

- [`scripts/is-verifiable.sh`](scripts/is-verifiable.sh), assesses whether the verification of a given a Dafny program (i.e., a .dfy file) runs successfully, in a nutshell, it runs Dafny's `verify` command and analyzes its output.

Usage example:

```bash
bash scripts/is-verifiable.sh \
  --input_file_path ../.third-parties/dafnybench/DafnyBench/dataset/ground_truth/630-dafny_tmp_tmpz2kokaiq_Solution.dfy \
  --output_file_path data/generated/is-verifiable/DafnyBench/630-dafny_tmp_tmpz2kokaiq_Solution/data.csv
```

**Note:** The script [`scripts/gen-is-verifiable-jobs.sh`](scripts/gen-is-verifiable-jobs.sh) automatizes the process of running the [`scripts/is-verifiable.sh`](scripts/is-verifiable.sh) script on **all** programs listed in [`data/generated/subjects.csv`](data/generated/subjects.csv)

- [`scripts/collect-commits.sh`](scripts/collect-commits.sh), given a set of GitHub URLs, this script collects the commits in each repository that match specific keywords (e.g., fix).

## Data

Note: the structure of each CVS file is explained in the [data/FILE-SPECS.md](data/FILE-SPECS.md) file.

- [`data/generated/subjects.csv`](data/generated/subjects.csv) set Dafny programs.

- [`data/generated/subjects-whitelist.csv`](data/generated/subjects-whitelist.csv) set of verifiable Dafny programs.

- [`data/generated/repositories.csv`](data/generated/repositories.csv) set of GitHub repositories with Dafny projects.

- [`data/generated/commits.csv`](data/generated/commits.csv) GitHub URL of commit messages that match specific keywords (e.g., fix).

## Statistics

<!-- TBA -->
