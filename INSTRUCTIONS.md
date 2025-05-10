# Instructions to repeat and reproduce the analyses and results in the associated paper

The following sections provides step-by-step instructions to repeat and reproduce the analyses, tables, and figures reported in the associated paper.

## Requirements

All commands / scripts have been tested and used on a Unix-based machine and therefore might not work on other operating systems, e.g., Windows. This document also assumes the reader is comfortable running bash commands and navigating in/out directories on the command line.

The subsequent analyses require the following tools to be installed and available on your machine (unless the [docker](https://www.docker.com) option is used):
- [GIT](https://git-scm.com) and [GNU wget](https://www.gnu.org/software/wget)
- [GNU Parallel](https://www.gnu.org/software/parallel)
- [R Project for Statistical Computing](https://www.r-project.org)

Visit the [REQUIREMENTS.md](REQUIREMENTS.md) file for more details.

## Setup

### [Docker](https://www.docker.com) option

For an easy setup, we recommend our [docker image](https://hub.docker.com/r/<USER>/TBA) that includes all scripts, data, and instructions required to [repeat and reproduce](https://www.acm.org/publications/policies/artifact-review-and-badging-current) our study. Otherwise, follow the setup instructions in the next section 'Non-Docker option'.

First, pull the docker image

```bash
docker pull <USER>/TBA
```

Second, connect to the docker image

```bash
docker run --interactive --tty --privileged \
  --volume $(pwd):/mutdafny-data \
  --workdir /mutdafny-data/ <USER>/TBA
```

which should lead you to the root directory of the artifact. Then, follow the following sections which provide step-by-step instructions on which commands to run to repeat and reproduce the experiments described in the associated paper.

### Non-[Docker](https://www.docker.com) option

In the top-level directory [`.third-parties/`](.third-parties/), run the following command

```bash
bash get-third-parties.sh # (~20 minutes)
```

In case the execution does not finished successfully, the script will print out a message informing the user of the error. One should follow the instructions to fix the error and re-run the script. In case the execution of the script finished successfully, one should see the message `DONE! All third parties have been successfully installed and configured.` on the stdout.

Visit the [INSTALL.md](INSTALL.md) file for more details.

## Experiments

Below you might find the step-by-step on how to execute the experiments described in our study for a single Dafny program and for **all** programs listed in [`subjects/data/generated/subjects.csv`](subjects/data/generated/subjects.csv). For the single Dafny program's step-by-step, start by initializing the following variables:

```bash
BENCHMARK_NAME="DafnyBench"
PROGRAM_NAME="630-dafny_tmp_tmpz2kokaiq_Solution"
MUTATION_OPERATOR="BOR"
```

**Note:** the step-by-step assumes you are running commands from the repository's root directory.

### 0. Verifiable Dafny programs

<!-- TODO: briefly describe why we need to perform this -->

To assess whether the running example Dafny program is verifiable one could run the following command:

```bash
bash "subjects/scripts/is-verifiable.sh" \
  --benchmark_name "$BENCHMARK_NAME" \
  --input_file_path ".third-parties/dafnybench/DafnyBench/dataset/ground_truth/$PROGRAM_NAME.dfy" \
  --output_file_path "subjects/data/generated/is-verifiable/$PROGRAM_NAME/data.csv"
```

which generates one CSV file (Note: the structure of each CVS file is explained in the [subjects/data/FILE-SPECS.md](subjects/data/FILE-SPECS.md) file):
- `subjects/data/generated/is-verifiable/$PROGRAM_NAME/data.csv`, runtime data of the execution of Dafny's `verify` command.

**Note:** The script [`subjects/scripts/gen-is-verifiable-jobs.sh`](subjects/scripts/gen-is-verifiable-jobs.sh) automatizes the process of running Dafny's `verify` command on **all** programs listed in [`subjects/data/generated/subjects.csv`](subjects/data/generated/subjects.csv). For instance,

1. Generate jobs, where each job is the execution of the [`subjects/scripts/is-verifiable.sh`](subjects/scripts/is-verifiable.sh) script on a given Dafny program, to be executed in parallel either using [GNU Parallel](https://www.gnu.org/software/parallel) or [Slurm](https://slurm.schedmd.com).

```bash
bash "subjects/scripts/gen-is-verifiable-jobs.sh" \
  --input_file_path "subjects/data/generated/subjects.csv" \
  --output_dir_path "subjects/data/generated/is-verifiable"
```

This would generate three top-level directories in the provided output dir (`jobs`, `logs`, and `data`) and create subdirectories, one for each Dafny program, i.e.:
- `jobs/<Dafny program name>/`
  * `jobs/<Dafny program name>/job.sh` which runs `subjects/scripts/is-verifiable.sh`.
- `logs/<Dafny program name>/`
  * `logs/<Dafny program name>/job.log` which keeps the stdout and stderr of the execution of the correspondent `job` script.
- `data/<Dafny program name>/`

2. Run jobs in parallel.

```bash
bash "utils/scripts/run-jobs.sh" \
  --jobs_dir_path "subjects/data/generated/is-verifiable/jobs" \
  --seconds_per_job 120 \
  --max_number_batches 128 \
  --memory 1024
```

This script splits the set of jobs created by the [`subjects/scripts/gen-is-verifiable-jobs.sh`](subjects/scripts/gen-is-verifiable-jobs.sh) script in batches (as some clusters might have a hard limit) and either run them using [GNU Parallel](https://www.gnu.org/software/parallel) or submit them to the cluster's workload manager, i.e., [Slurm](https://slurm.schedmd.com). If the machine supports the [Slurm](https://slurm.schedmd.com) workload manager, jobs are submitted to it. If not, jobs are executed using [GNU Parallel](https://www.gnu.org/software/parallel).

**Tip:** To compute the number of jobs that finished successfully one could run the following command:

```bash
find "subjects/data/generated/is-verifiable/logs" -type f -name "job.log" -exec grep -l "^DONE" {} \; | wc -l
```

3. Once all jobs have finished successfully one could compute the set of verifiable Dafny programs by running the following command:

```bash
echo "benchmark_name,program_name" > "subjects/data/generated/subjects-whitelist.csv"
find "subjects/data/generated/is-verifiable/data" -type f -name "data.csv" -exec grep "^.*,.*,1,.*$" {} \; | cut -f1,2 -d',' >> "subjects/data/generated/subjects-whitelist.csv"
```

### 1. Generation of mutation targets

<!-- TODO: add a brief description of the procedure to generate the targets -->

To generate the mutation targets for the running example Dafny program one could run the following command:

```bash
bash "mutation/scripts/run-scan.sh" \
  --benchmark_name "$BENCHMARK_NAME" \
  --input_file_path ".third-parties/dafnybench/DafnyBench/dataset/ground_truth/$PROGRAM_NAME.dfy" \
  --mutation_operator "$MUTATION_OPERATOR" \
  --output_directory_path "mutation/data/generated/scan/data/$MUTATION_OPERATOR/$BENCHMARK_NAME/$PROGRAM_NAME/"
```

which generates two CSV files (Note: the structure of each CVS file is explained in the [mutation/data/FILE-SPECS.md](mutation/data/FILE-SPECS.md) file):
- `data/generated/scan/stats/$MUTATION_OPERATOR/$BENCHMARK_NAME/$PROGRAM_NAME/data.csv`, runtime data of the execution of MutDafny's `scan` command.
- `data/generated/scan/stats/$MUTATION_OPERATOR/$BENCHMARK_NAME/$PROGRAM_NAME/targets.csv`, set of mutation targets.

and one helper file (later used in the mutation analysis):
- `data/generated/scan/stats/$MUTATION_OPERATOR/$BENCHMARK_NAME/$PROGRAM_NAME/helpers.txt`. <!-- TODO: add a brief description -->

**Note:** The script [`mutation/scripts/gen-scan-jobs.sh`](mutation/scripts/gen-scan-jobs.sh) automatizes the process of running MutDafny's `scan` command on **all** programs listed in [`subjects/data/generated/subjects-whitelist.csv`](subjects/data/generated/subjects-whitelist.csv) on one or more mutation operators. For instance,

1. Generate jobs, where each job is the execution of the [`mutation/scripts/run-scan.sh`](mutation/scripts/run-scan.sh) script on a given Dafny program and mutation operator, to be executed in parallel either using [GNU Parallel](https://www.gnu.org/software/parallel) or [Slurm](https://slurm.schedmd.com).

```bash
bash "mutation/scripts/gen-scan-jobs.sh" \
  --input_file_path "subjects/data/generated/subjects-whitelist.csv" \
  --mutation_operators "BOR,BBR,UOI,UOD,LVR,EVR,LSR,LBI,CIR,SDL" \
  --output_dir_path "mutation/data/generated/scan"
```

This would generate three top-level directories in the provided output dir (`jobs`, `logs`, and `data`) and create subdirectories, one for each combination of mutation operator and Dafny program, i.e.:
- `jobs/<mutation operator, BOR|BBR|UOI|UOD|LVR|EVR|LSR|LBI|CIR|SDL>/<Benchmark name>/<Dafny program name>/`
  * `jobs/<mutation operator, BOR|BBR|UOI|UOD|LVR|EVR|LSR|LBI|CIR|SDL>/<Benchmark name>/<Dafny program name>/job.sh` which runs `mutation/scripts/run-scan.sh`.
- `logs/<mutation operator, BOR|BBR|UOI|UOD|LVR|EVR|LSR|LBI|CIR|SDL>/<Benchmark name>/<Dafny program name>/`
  * `logs/<mutation operator, BOR|BBR|UOI|UOD|LVR|EVR|LSR|LBI|CIR|SDL>/<Benchmark name>/<Dafny program name>/job.log` which keeps the stdout and stderr of the execution of the correspondent `job` script.
- `data/<mutation operator, BOR|BBR|UOI|UOD|LVR|EVR|LSR|LBI|CIR|SDL>/<Benchmark name>/<Dafny program name>/`

2. Run jobs in parallel.

```bash
bash "utils/scripts/run-jobs.sh" \
  --jobs_dir_path "mutation/data/generated/scan/jobs" \
  --seconds_per_job 60 \
  --max_number_batches 128 \
  --memory 1024
```

This script splits the set of jobs created by the [`mutation/scripts/gen-scan-jobs.sh`](mutation/scripts/gen-scan-jobs.sh) script in batches (as some clusters might have a hard limit) and either run them using [GNU Parallel](https://www.gnu.org/software/parallel) or submit them to the cluster's workload manager, i.e., [Slurm](https://slurm.schedmd.com). If the machine supports the [Slurm](https://slurm.schedmd.com) workload manager, jobs are submitted to it. If not, jobs are executed using [GNU Parallel](https://www.gnu.org/software/parallel).

**Tip:** To compute the number of jobs that finished successfully one could run the following command:

```bash
find "mutation/data/generated/scan/logs" -type f -name "job.log" -exec grep -l "^DONE" {} \; | wc -l
```

**Tip:** If some jobs finished unsuccessfully due to cluster's timeouts or simply because they ran out of memory, you could re-run the [`utils/scripts/run-jobs.sh`](utils/scripts/run-jobs.sh) script with a different time/memory value. (Note: the [`utils/scripts/run-jobs.sh`](utils/scripts/run-jobs.sh) script would only re-run jobs that finished unsuccessfully.)
For example, twice the time and memory per job:

```bash
bash "utils/scripts/run-jobs.sh" \
  --jobs_dir_path "mutation/data/generated/scan/jobs" \
  --seconds_per_job 120 \
  --max_number_batches 128 \
  --memory 2048
```

### 2. Mutation analysis

<!-- TODO: add a brief description of (a) the actual generation of mutants and (b) the verification step -->

The script to run mutation analysis are very similar to the ones to generate of mutation targets. To run mutation analysis for the running example Dafny program one could run the following command:

```bash
bash "mutation/scripts/run-mut.sh" \
  --benchmark_name "$BENCHMARK_NAME" \
  --input_file_path ".third-parties/dafnybench/DafnyBench/dataset/ground_truth/$PROGRAM_NAME.dfy" \
  --targets_file_path "mutation/data/generated/scan/data/$MUTATION_OPERATOR/$BENCHMARK_NAME/$PROGRAM_NAME/targets.csv" \
  --helpers_file_path "mutation/data/generated/scan/data/$MUTATION_OPERATOR/$BENCHMARK_NAME/$PROGRAM_NAME/helpers.txt" \
  --output_file_path "mutation/data/generated/mut/data/$MUTATION_OPERATOR/$BENCHMARK_NAME/$PROGRAM_NAME/data.csv" \
  --output_directory_path "mutation/data/generated/mut/mutants/$MUTATION_OPERATOR/$BENCHMARK_NAME/$PROGRAM_NAME/"
```

which generates one CSV file (Note: the structure of each CVS file is explained in the [mutation/data/FILE-SPECS.md](mutation/data/FILE-SPECS.md) file):
- `mutation/data/generated/mut/data/$MUTATION_OPERATOR/$BENCHMARK_NAME/$PROGRAM_NAME/data.csv`, runtime data of the execution of MutDafny's `mut` command.

and .dfy files in the provided output directory, one per mutant generated by MutDafny.

**Note:** The script [`mutation/scripts/gen-mut-jobs.sh`](mutation/scripts/gen-mut-jobs.sh) automatizes the process of running MutDafny's `mut` command on **all** programs listed in [`subjects/data/generated/subjects-whitelist.csv`](subjects/data/generated/subjects-whitelist.csv) on one or more mutation operators. For instance,

1. Generate jobs, where each job is the execution of the [`mutation/scripts/run-mut.sh`](mutation/scripts/run-mut.sh) script on a given Dafny program and mutation operator, to be executed in parallel either using [GNU Parallel](https://www.gnu.org/software/parallel) or [Slurm](https://slurm.schedmd.com).

```bash
bash "mutation/scripts/gen-mut-jobs.sh" \
  --input_file_path "subjects/data/generated/subjects-whitelist.csv" \
  --mutation_operators "BOR,BBR,UOI,UOD,LVR,EVR,LSR,LBI,CIR,SDL" \
  --scan_dir_path "mutation/data/generated/scan" \
  --output_dir_path "mutation/data/generated/mut"
```

This would generate four top-level directories in the provided output dir (`jobs`, `logs`, `mutants`, and `data`) and create subdirectories, one for each combination of mutation operator and Dafny program, i.e.:
- `jobs/<mutation operator, BOR|BBR|UOI|UOD|LVR|EVR|LSR|LBI|CIR|SDL>/<Benchmark name>/<Dafny program name>/`
  * `jobs/<mutation operator, BOR|BBR|UOI|UOD|LVR|EVR|LSR|LBI|CIR|SDL>/<Benchmark name>/<Dafny program name>/job.sh` which runs `mutation/scripts/run-scan.sh`.
- `logs/<mutation operator, BOR|BBR|UOI|UOD|LVR|EVR|LSR|LBI|CIR|SDL>/<Benchmark name>/<Dafny program name>/`
  * `logs/<mutation operator, BOR|BBR|UOI|UOD|LVR|EVR|LSR|LBI|CIR|SDL>/<Benchmark name>/<Dafny program name>/job.log` which keeps the stdout and stderr of the execution of the correspondent `job` script.
- `mutants/<mutation operator, BOR|BBR|UOI|UOD|LVR|EVR|LSR|LBI|CIR|SDL>/<Benchmark name>/<Dafny program name>/`
- `data/<mutation operator, BOR|BBR|UOI|UOD|LVR|EVR|LSR|LBI|CIR|SDL>/<Benchmark name>/<Dafny program name>/`

2. Run jobs in parallel.

```bash
bash "utils/scripts/run-jobs.sh" \
  --jobs_dir_path "mutation/data/generated/mut/jobs" \
  --seconds_per_job 60 \
  --max_number_batches 128 \
  --memory 1024
```

This script splits the set of jobs created by the [`mutation/scripts/gen-mut-jobs.sh`](mutation/scripts/gen-mut-jobs.sh) script in batches (as some clusters might have a hard limit) and either run them using [GNU Parallel](https://www.gnu.org/software/parallel) or submit them to the cluster's workload manager, i.e., [Slurm](https://slurm.schedmd.com). If the machine supports the [Slurm](https://slurm.schedmd.com) workload manager, jobs are submitted to it. If not, jobs are executed using [GNU Parallel](https://www.gnu.org/software/parallel).

**Tip:** To compute the number of jobs that finished successfully one could run the following command:

```bash
find "mutation/data/generated/mut/logs" -type f -name "job.log" -exec grep -l "^DONE" {} \; | wc -l
```

**Tip:** If some jobs finished unsuccessfully due to cluster's timeouts or simply because they ran out of memory, you could re-run the [`utils/scripts/run-jobs.sh`](utils/scripts/run-jobs.sh) script with a different time/memory value. (Note: the [`utils/scripts/run-jobs.sh`](utils/scripts/run-jobs.sh) script would only re-run jobs that finished unsuccessfully.)
For example, twice the time and memory per job:

```bash
bash "utils/scripts/run-jobs.sh" \
  --jobs_dir_path "mutation/data/generated/mut/jobs" \
  --seconds_per_job 120 \
  --max_number_batches 128 \
  --memory 2048
```
