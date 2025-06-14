# ------------------------------------------------------------------------------
# This script gathers the data from several scan executions into a single file.
# operator.
#
# Usage:
# Rscript collect-scan-data.R
#   <data dir path, e.g., ../../mutation/data/generated>
#   <scan data file list, e.g., exec1-scan-data.csv,exec2-scan-data.csv,exec3-scan-data.csv>
#   <mut data file list, e.g., exec1-mut-data.csv,exec2-mut-data.csv,exec3-mut-data.csv>
#   <scan output file path, e.g., ../../mutation/data/generated/scan-data.csv>
#   <mut output file path, e.g., ../../mutation/data/generated/mut-data.csv>
# ------------------------------------------------------------------------------

source('../statistics/utils.R')
library('dplyr', lib.loc=local_library)
library('withr', lib.loc=local_library)

# ------------------------------------------------------------------------- Args

args = commandArgs(trailingOnly=TRUE)
if (length(args) != 5) {
  stop('USAGE: Rscript collect-data.R <data dir path, e.g., ../../mutation/data/generated> 
    <scan data file list, e.g., exec1-scan-data.csv,exec2-scan-data.csv,exec3-scan-data.csv> 
    <mut data file list, e.g., exec1-mut-data.csv,exec2-mut-data.csv,exec3-mut-data.csv> 
    <output dir path, e.g., ../../mutation/data/generated/scan-data.csv> 
    <mut output file path, e.g., ../../mutation/data/generated/mut-data.csv>'
  )
}

# Args
DATA_DIR_PATH  <- args[1]
SCAN_FILE_LIST <- strsplit(args[2], ",")[[1]]
MUT_FILE_LIST <- strsplit(args[3], ",")[[1]]
SCAN_OUTPUT_FILE_PATH <- args[4]
MUT_OUTPUT_FILE_PATH <- args[5]

# ------------------------------------------------------------------------- Main

scan_file_paths <- file.path(DATA_DIR_PATH, SCAN_FILE_LIST)
mut_file_paths <- file.path(DATA_DIR_PATH, MUT_FILE_LIST)

# -------- Scan

join <- Reduce(rbind, lapply(scan_file_paths, load_CSV))

# remove 20% highest values and 20% lowest values
n_to_remove = round(0.2 * length(SCAN_FILE_LIST))
filtered <- join %>%
  dplyr::group_by(benchmark_name, program_name, mutation_operator) %>%
  dplyr::arrange(scan_time, .by_group = TRUE) %>%
  dplyr::mutate(row_rank = row_number()) %>%
  dplyr::filter(    
    row_rank > n_to_remove &
    row_rank <= (length(SCAN_FILE_LIST) - n_to_remove)
  ) %>%
  dplyr::select(-row_rank) %>%
  dplyr::ungroup()

scan_averages <- filtered %>%
  dplyr::group_by(benchmark_name, program_name, mutation_operator) %>%
  dplyr::summarise(
    parsing_time = mean(parsing_time),
    plugin_time = mean(plugin_time),
    resolution_time = mean(resolution_time),
    verification_time = mean(verification_time),
    number_of_targets = get_mode(number_of_targets),
    scan_time = mean(scan_time),
    .groups = 'drop'
  )

# -------- Mut

join <- Reduce(rbind, lapply(mut_file_paths, load_CSV))

# remove 20% highest values and 20% lowest values
n_to_remove = round(0.2 * length(MUT_FILE_LIST))
filtered <- join %>%
  dplyr::group_by(benchmark_name, program_name, mutation_position, mutation_operator, mutation) %>%
  dplyr::arrange(mut_time, .by_group = TRUE) %>%
  dplyr::mutate(row_rank = row_number()) %>%
  dplyr::filter(    
    row_rank > n_to_remove &
    row_rank <= (length(MUT_FILE_LIST) - n_to_remove)
  ) %>%
  dplyr::select(-row_rank) %>%
  dplyr::ungroup()

mut_averages <- filtered %>%
  dplyr::group_by(benchmark_name, program_name, mutation_position, mutation_operator, mutation) %>%
  dplyr::summarise(
    status = get_mode(status),
    parsing_time = mean(parsing_time),
    plugin_time = mean(plugin_time),
    resolution_time = mean(resolution_time),
    verification_time = mean(verification_time),
    mut_time = mean(mut_time),
    .groups = 'drop'
  )

# -------- Save

write.csv(scan_averages, file = SCAN_OUTPUT_FILE_PATH, row.names = FALSE)
write.csv(mut_averages, file = MUT_OUTPUT_FILE_PATH, row.names = FALSE)
