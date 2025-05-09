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

- [`scripts/collect-whitelist-subjects.sh`](scripts/collect-whitelist-subjects.sh), collects the set of Dafny programs defined in the [`data/generated/subjects.csv`](data/generated/subjects.csv) that can be verified successfully.

- [`scripts/collect-commits.sh`](scripts/collect-commits.sh), given a set of GitHub URLs, this script collects the commits in each repository that match specific keywords (e.g., fix).

## Data

- [`data/generated/subjects.csv`](data/generated/subjects.csv) set Dafny programs.

- [`data/generated/subjects-whitelist.csv`](data/generated/subjects-whitelist.csv) set of verifiable Dafny programs.

- [`data/generated/repositories.csv`](data/generated/repositories.csv) set of GitHub repositories with Dafny projects.

- [`data/generated/commits.csv`](data/generated/commits.csv) GitHub URL of commit messages that match specific keywords (e.g., fix).

## Statistics

<!-- TBA -->
