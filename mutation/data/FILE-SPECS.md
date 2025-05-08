# Specifications of data files

## [`generated/scan/stats/<mutation operator, BOR|BBR|UOI|UOD|LVR|EVR|LSR|LBI|CIR|SDL>/<Dafny program name>/elapsed-time.csv`]

- `parsing_time`: time in milliseconds to <TBA>
  * numerical, e.g., 1

- `plugin_time`: time in milliseconds to <TBA>
  * numerical, e.g., 3

- `resolution_time`: time in milliseconds to <TBA>
  * numerical, e.g., 7

- `verification_time`: time in milliseconds to <TBA>
  * numerical, e.g., 9

## [`generated/scan/stats/<mutation operator, BOR|BBR|UOI|UOD|LVR|EVR|LSR|LBI|CIR|SDL>/<Dafny program name>/targets.csv`]

<!-- <TBA> -->

## [`generated/scan/stats/<mutation operator, BOR|BBR|UOI|UOD|LVR|EVR|LSR|LBI|CIR|SDL>/<Dafny program name>/data.csv`]

- `project_name`: Project name
  * factor, e.g., 630-dafny_tmp_tmpz2kokaiq_Solution

- `mutation_operator`
  * factor: BOR, BBR, UOI, UOD, LVR, EVR, LSR, LBI, CIR, or SDL

- `parsing_time`: time in milliseconds to <TBA>
  * numerical, e.g., 1

- `plugin_time`: time in milliseconds to <TBA>
  * numerical, e.g., 3

- `resolution_time`: time in milliseconds to <TBA>
  * numerical, e.g., 7

- `verification_time`: time in milliseconds to <TBA>
  * numerical, e.g., 9

- `number_of_targets`: number of targets
  * numerical, e.g., 899

- `scan_time`: total time in milliseconds to run MutDafny's scan command
  * numerical, e.g., 7182
