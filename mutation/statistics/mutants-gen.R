# ------------------------------------------------------------------------------
# This script computes and plots the distribution MutDafny's runtime at generating
# mutants.
#
# Usage:
# Rscript mutants-gen.R
#   <scan data file path, e.g., ../data/generated/scan-data.csv>
#   <mutation data file path, e.g., ../data/generated/mut-data.csv>
#   <output dir path, e.g., ../data/generated>
# ------------------------------------------------------------------------------

source('../../utils/statistics/utils.R')
library('dplyr', lib.loc=local_library)
library('ggplot2', lib.loc=local_library)
library('ggbeeswarm', lib.loc=local_library)
library('scales', lib.loc=local_library)

# ------------------------------------------------------------------------- Args

args = commandArgs(trailingOnly=TRUE)
if (length(args) != 3) {
  stop('USAGE: Rscript mutants-gen.R <scan data file path, e.g., ../data/generated/scan-data.csv> <mutation data file path, e.g., ../data/generated/mut-data.csv> <output dir path, e.g., ../data/generated>')
}

# Args
SCAN_DATA_FILE_PATH <- args[1] # benchmark_name,program_name,mutation_operator,parsing_time,plugin_time,resolution_time,verification_time,number_of_targets,scan_time
MUT_DATA_FILE_PATH  <- args[2] # benchmark_name,program_name,mutation_position,mutation_operator,mutation,status,parsing_time,plugin_time,resolution_time,verification_time,run_time
OUTPUT_DIR_PATH     <- args[3]

# ------------------------------------------------------------------------- Main

# Load data
scan_data <- load_CSV(SCAN_DATA_FILE_PATH)
mut_data  <- load_CSV(MUT_DATA_FILE_PATH)

# Discard invalid mutants
mut_data <- mut_data[mut_data$'status' != 'invalid', ]

# Keep some columns
scan_data <- scan_data[ , (names(scan_data) %in% c('benchmark_name', 'program_name', 'mutation_operator', 'parsing_time', 'plugin_time', 'resolution_time', 'verification_time', 'scan_time'))]
mut_data  <- mut_data[ , (names(mut_data) %in% c('benchmark_name', 'program_name', 'mutation_operator', 'status', 'plugin_time', 'verification_time', 'mut_time'))]

# Merge data by benchmark_name, program_name, mutation_operator
df <- merge(scan_data, mut_data, by=c('benchmark_name', 'program_name', 'mutation_operator'))
df <- df %>%
  rename(
    scan_plugin_time = plugin_time.x,
    mut_plugin_time = plugin_time.y,
    scan_verification_time = verification_time.x,
    mut_verification_time = verification_time.y
  )

# Compute runtime
df$'runtime' <- df$'mut_time' - df$'mut_verification_time'
# Convert milliseconds to seconds
df$'runtime' <- df$'runtime' * 0.001
df$'mut_plugin_time' <- df$'mut_plugin_time' * 0.001
df$'mut_time' <- df$'mut_time' * 0.001

# -------- Overall program mutation time

OUTPUT_FILE_PATH <- paste0(OUTPUT_DIR_PATH, '/', 'distribution-overall-runtime-programs-gen.pdf')

# Remove any existing output file and create a new one
unlink(OUTPUT_FILE_PATH)
pdf(file=OUTPUT_FILE_PATH, family='Helvetica', width=6, height=2)

# Compute average scan_time per program and total
scan_times_df <- scan_data %>%
  dplyr::filter(mutation_operator == "ALL") %>%
  dplyr::select(benchmark_name, program_name, plugin_time, scan_time)
avg_scan_time <- mean(scan_times_df$scan_time) * 0.001
med_scan_time <- median(scan_times_df$scan_time) * 0.001

# Compute total runtime per program
total_gen_times_df <- df %>%
  dplyr::group_by(benchmark_name, program_name) %>%
  dplyr::summarise(
    total_mut_time = sum(runtime)
  ) %>%
  # Join with scan_times
  dplyr::left_join(scan_times_df, by = c("benchmark_name", "program_name")) %>%
  # Calculate total runtime
  dplyr::mutate(
    total_runtime = total_mut_time + scan_time * 0.001
  )

print(summary(total_gen_times_df$'total_runtime'))
print(total_gen_times_df[total_gen_times_df$'total_runtime' == min(total_gen_times_df$'total_runtime'), ])

# Calculate mean, median, and max runtimes
mean_time   <- mean(total_gen_times_df$'total_runtime')
median_time <- median(total_gen_times_df$'total_runtime')
max_time    <- max(total_gen_times_df$'total_runtime')

p <- ggplot(total_gen_times_df, aes(y=total_runtime)) + geom_boxplot()
# Horizontal box plot
p <- p + coord_flip()
# Add vertical line for mean scan_time
p <- p + geom_hline(yintercept=avg_scan_time, linetype='dashed', color='brown')
# Add text label to the line
p <- p + annotate('text', x=0, y=avg_scan_time, vjust=-3.5, hjust=-0.05,
           label=paste0('Mean scan time = ', sprintf('%.2f', round(avg_scan_time, 2))),
           size=4, color='brown')
# Add vertical line for median scan_time
p <- p + geom_hline(yintercept=med_scan_time, linetype='dashed', color='blue')
# Add text label to the line
p <- p + annotate('text', x=0, y=med_scan_time, vjust=-1.5, hjust=-0.155,
           label=paste0('Median scan time = ', sprintf('%.2f', round(med_scan_time, 2))),
           size=4, color='blue')
# Scale y-axis
p <- p + scale_y_log10(
  breaks=scales::log_breaks(base=10, n=12),
  labels=scales::label_comma()
)
# Set labs
p <- p + labs(x='', y='Runtime (seconds, log10 scale)')
# Remove axis
p <- p + theme(axis.title.y = element_blank(), axis.text.y = element_blank(), axis.ticks.y = element_blank())
# Add text values
p <- p + annotate('text', x=Inf, y=Inf, hjust=1, vjust=1,
           label=paste0(#
             'Median = ', sprintf('%.2f', round(median_time, 2)), '\n',
             'Mean = ', sprintf('%.2f', round(mean_time, 2)), '\n',
             'Max = ', sprintf('%.2f', round(max_time, 2))
           ),
           size=4, color='black')
# Print plot
print(p)

# Close output file
dev.off()
# Embed fonts
embed_fonts_in_a_pdf(OUTPUT_FILE_PATH)

# -------- Overall program total time (with verification)

OUTPUT_FILE_PATH <- paste0(OUTPUT_DIR_PATH, '/', 'distribution-overall-runtime-programs-total.pdf')

# Remove any existing output file and create a new one
unlink(OUTPUT_FILE_PATH)
pdf(file=OUTPUT_FILE_PATH, family='Helvetica', width=6, height=2)

# Compute total runtime per program
total_times_df <- df %>%
  dplyr::group_by(benchmark_name, program_name) %>%
  dplyr::summarise(
    total_mut_time = sum(mut_time)
  ) %>%
  # Join with the scan_time data
  dplyr::left_join(scan_times_df, by = c("benchmark_name", "program_name")) %>%
  # Calculate total runtime
  dplyr::mutate(
    total_runtime = total_mut_time + scan_time * 0.001
  )

print(summary(total_times_df$'total_runtime'))
print(total_times_df[total_times_df$'total_runtime' == min(total_times_df$'total_runtime'), ])

# Calculate mean, median, and max runtimes
mean_time   <- mean(total_times_df$'total_runtime')
median_time <- median(total_times_df$'total_runtime')
max_time    <- max(total_times_df$'total_runtime')

p <- ggplot(total_times_df, aes(y=total_runtime)) + geom_boxplot()
# Horizontal box plot
p <- p + coord_flip()
# Scale y-axis
p <- p + scale_y_log10(
  breaks=scales::log_breaks(base=10, n=12),
  labels=scales::label_comma()
)
# Set labs
p <- p + labs(x='', y='Runtime (seconds, log10 scale)')
# Remove axis
p <- p + theme(axis.title.y = element_blank(), axis.text.y = element_blank(), axis.ticks.y = element_blank())
# Add text values
p <- p + annotate('text', x=Inf, y=Inf, hjust=1, vjust=1,
           label=paste0(#
             'Median = ', sprintf('%.2f', round(median_time, 2)), '\n',
             'Mean = ', sprintf('%.2f', round(mean_time, 2)), '\n',
             'Max = ', sprintf('%.2f', round(max_time, 2))
           ),
           size=4, color='black')
# Print plot
print(p)

# Close output file
dev.off()
# Embed fonts
embed_fonts_in_a_pdf(OUTPUT_FILE_PATH)

# -------- Overall plugin time (no verification and no resolution)

plugin_times_df <- df %>%
  dplyr::group_by(benchmark_name, program_name) %>%
  dplyr::summarise(
    total_mut_time = sum(mut_plugin_time)
  ) %>%
  # Join with the scan_time data
  dplyr::left_join(scan_times_df, by = c("benchmark_name", "program_name")) %>%
  # Calculate total runtime
  dplyr::mutate(
    total_runtime = total_mut_time + plugin_time * 0.001
  )

mutants_verif_times <- df %>%
  dplyr::group_by(benchmark_name, program_name) %>%
  dplyr::summarise(
    total_verif_time = sum(mut_verification_time)
  ) %>%
  dplyr::mutate(
    total_runtime = total_verif_time * 0.001
  )

# -------- Combined

OUTPUT_FILE_PATH <- paste0(OUTPUT_DIR_PATH, '/', 'distribution-overall-runtime-programs-combined.pdf')

# Remove any existing output file and create a new one
unlink(OUTPUT_FILE_PATH)
pdf(file=OUTPUT_FILE_PATH, family='Helvetica', width=7, height=5)

# Prepare the data for combined plot
combined_df <- bind_rows(
  plugin_times_df %>% mutate(type = "Plugin"),
  total_gen_times_df %>% mutate(type = "Mutant generation"),
  mutants_verif_times %>% mutate(type = "Mutation analysis"),
  total_times_df %>% mutate(type = "Total")
) %>%
mutate(type = factor(
  type, 
  levels = c("Plugin", "Mutant generation", "Mutation analysis", "Total"),
  ordered = TRUE
))

# Calculate global min and max for consistent scaling
global_min <- min(min(plugin_times_df$total_runtime), min(total_gen_times_df$total_runtime), min(mutants_verif_times$total_runtime), min(total_times_df$total_runtime))
global_max <- max(max(plugin_times_df$total_runtime), max(total_gen_times_df$total_runtime), max(mutants_verif_times$total_runtime), max(total_times_df$total_runtime))

# Create combined plot
p <- ggplot(combined_df, aes(x = type, y = total_runtime, fill = type)) + 
  geom_boxplot() +
  coord_flip() +
  scale_y_log10(
    breaks = scales::log_breaks(base = 10, n = 12),
    labels = scales::label_comma(),
    limits = c(global_min, global_max)  # Ensure same scale for both
  ) +
  labs(
    x = '', 
    y = 'Runtime (seconds, log10 scale)',
    fill = 'Type'
  ) +
  theme(
    axis.title.y = element_blank(),
    axis.text.y = element_blank(),
    axis.ticks.y = element_blank(),
    legend.position = "bottom"
  ) +
  scale_fill_manual(values = c("Plugin" = "goldenrod", "Mutant generation" = "sandybrown", "Mutation analysis" = "mediumseagreen", "Total" = "cornflowerblue"))

# Calculate statistics for annotation
plugin_stats <- plugin_times_df$total_runtime
gen_stats <- total_gen_times_df$total_runtime
mut_verif_stats <- mutants_verif_times$total_runtime
total_stats <- total_times_df$total_runtime

# Add text annotations
p <- p + annotate('text', x = Inf, y = Inf, hjust = 1, vjust = 1,
           label = paste0(
              'Plugin time\n',
             'Median = ', sprintf('%.2f', round(median(plugin_stats), 2)), '\n',
             'Mean = ', sprintf('%.2f', round(mean(plugin_stats), 2)), '\n',
             'Max = ', sprintf('%.2f', round(max(plugin_stats), 2)), '\n',
             '\n',
             'Generation time\n',
             'Median = ', sprintf('%.2f', round(median(gen_stats), 2)), '\n',
             'Mean = ', sprintf('%.2f', round(mean(gen_stats), 2)), '\n',
             'Max = ', sprintf('%.2f', round(max(gen_stats), 2)), '\n',
             '\n',
              'Mutation analysis time\n',
             'Median = ', sprintf('%.2f', round(median(mut_verif_stats), 2)), '\n',
             'Mean = ', sprintf('%.2f', round(mean(mut_verif_stats), 2)), '\n',
             'Max = ', sprintf('%.2f', round(max(mut_verif_stats), 2)), '\n',
             '\n',
             'Total time\n',
             'Median = ', sprintf('%.2f', round(median(total_stats), 2)), '\n',
             'Mean = ', sprintf('%.2f', round(mean(total_stats), 2)), '\n',
             'Max = ', sprintf('%.2f', round(max(total_stats), 2))
           ),
           size = 3, color = 'black')

# Print plot
print(p)

# Close output file
dev.off()
# Embed fonts
embed_fonts_in_a_pdf(OUTPUT_FILE_PATH)

# -------- Mutation time per mutation operator

OUTPUT_FILE_PATH <- paste0(OUTPUT_DIR_PATH, '/', 'distribution-runtime-operators-gen.pdf')

# Remove any existing output file and create a new one
unlink(OUTPUT_FILE_PATH)
pdf(file=OUTPUT_FILE_PATH, family='Helvetica', width=11, height=10)

scan_time_components_df <- scan_data %>%
  dplyr::filter(mutation_operator == "ALL") %>%
  dplyr::select(benchmark_name, program_name, parsing_time, resolution_time, verification_time)

operator_times_df <- df %>%
  dplyr::group_by(benchmark_name, program_name, mutation_operator) %>%
  dplyr::summarise(
    total_mut_time = sum(runtime),
    plugin_time = first(scan_plugin_time),
    num_mutants = n()
  ) %>%
  # Join with scan_times
  dplyr::left_join(scan_time_components_df, by = c("benchmark_name", "program_name")) %>%
  # Calculate total runtime
  dplyr::mutate(
    total_runtime = total_mut_time + (parsing_time + plugin_time + resolution_time + verification_time) * 0.001,
    avg_runtime = total_runtime / num_mutants
  )

print(summary(operator_times_df$'total_runtime'))
print(operator_times_df[operator_times_df$'total_runtime' == min(operator_times_df$'total_runtime'), ])

# Calculate mean, median, and max number of runtime
mean_runtimes   <- mean(operator_times_df$'total_runtime')
median_runtimes <- median(operator_times_df$'total_runtime')
max_runtimes    <- max(operator_times_df$'total_runtime')

# Distribution of runtime per mutation operator
p <- ggplot(operator_times_df, aes(x=mutation_operator, y=total_runtime)) + geom_boxplot() #+ facet_wrap(~ benchmark_name, scales='free_y')
# Spreads points nicely without as much overlap
p <- p + geom_quasirandom(alpha=0.2, size=0.7)
# Add horizontal line for mean runtime
p <- p + geom_hline(yintercept=mean_runtimes, linetype='dashed', color='brown')
# Add text label to the line, anchored at first bin (leftmost)
p <- p + annotate('text', x=0, y=mean_runtimes, vjust=-0.5, hjust=0,
           label=paste0('Mean = ', sprintf('%.2f', round(mean_runtimes, 2))),
           size=4, color='brown')
# Add horizontal line for median runtime
p <- p + geom_hline(yintercept=median_runtimes, linetype='dashed', color='blue')
# Add text label to the line, anchored at first bin (leftmost)
p <- p + annotate('text', x=0, y=median_runtimes, vjust=-0.5, hjust=0,
           label=paste0('Median = ', sprintf('%.2f', round(median_runtimes, 2))),
           size=4, color='blue')
# Add horizontal line for max runtime
p <- p + geom_hline(yintercept=max_runtimes, linetype='dashed', color='red')
# Add text label to the line, anchored at first bin (leftmost)
p <- p + annotate('text', x=0, y=max_runtimes, vjust=-0.5, hjust=0,
           label=paste0('Max = ', sprintf('%.2f', round(max_runtimes, 2))),
           size=4, color='red')
# Scale y-axis
p <- p + scale_y_log10(
  breaks=scales::log_breaks(base=10, n=15),
  labels=scales::label_comma()
)
# Set labs
p <- p + labs(x='Mutation Operator', y='Total mutant generation runtime (seconds, log10 scale)')
# Print plot
print(p)

# Close output file
dev.off()
# Embed fonts
embed_fonts_in_a_pdf(OUTPUT_FILE_PATH)

# -------- Average Mutation time per mutation operator

OUTPUT_FILE_PATH <- paste0(OUTPUT_DIR_PATH, '/', 'distribution-runtime-operators-gen-avg.pdf')

# Remove any existing output file and create a new one
unlink(OUTPUT_FILE_PATH)
pdf(file=OUTPUT_FILE_PATH, family='Helvetica', width=11, height=10)

# Calculate mean, median, and max number of runtime
mean_runtimes   <- mean(operator_times_df$'avg_runtime')
median_runtimes <- median(operator_times_df$'avg_runtime')
max_runtimes    <- max(operator_times_df$'avg_runtime')

# Distribution of runtime per mutation operator
p <- ggplot(operator_times_df, aes(x=mutation_operator, y=avg_runtime)) + geom_boxplot() #+ facet_wrap(~ benchmark_name, scales='free_y')
# Spreads points nicely without as much overlap
p <- p + geom_quasirandom(alpha=0.2, size=0.7)
# Add horizontal line for mean runtime
p <- p + geom_hline(yintercept=mean_runtimes, linetype='dashed', color='brown')
# Add text label to the line, anchored at first bin (leftmost)
p <- p + annotate('text', x=0, y=mean_runtimes, vjust=-0.5, hjust=0,
           label=paste0('Mean = ', sprintf('%.2f', round(mean_runtimes, 2))),
           size=4, color='brown')
# Add horizontal line for median runtime
p <- p + geom_hline(yintercept=median_runtimes, linetype='dashed', color='blue')
# Add text label to the line, anchored at first bin (leftmost)
p <- p + annotate('text', x=0, y=median_runtimes, vjust=-0.5, hjust=0,
           label=paste0('Median = ', sprintf('%.2f', round(median_runtimes, 2))),
           size=4, color='blue')
# Add horizontal line for max runtime
p <- p + geom_hline(yintercept=max_runtimes, linetype='dashed', color='red')
# Add text label to the line, anchored at first bin (leftmost)
p <- p + annotate('text', x=0, y=max_runtimes, vjust=-0.5, hjust=0,
           label=paste0('Max = ', sprintf('%.2f', round(max_runtimes, 2))),
           size=4, color='red')
# Scale y-axis
p <- p + scale_y_log10(
  breaks=scales::log_breaks(base=10, n=15),
  labels=scales::label_comma()
)
# Set labs
p <- p + labs(x='Mutation Operator', y='Average mutant generation runtime (seconds, log10 scale)')
# Print plot
print(p)

# Close output file
dev.off()
# Embed fonts
embed_fonts_in_a_pdf(OUTPUT_FILE_PATH)

# EOF
