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
scan_data <- scan_data[ , (names(scan_data) %in% c('benchmark_name', 'program_name', 'mutation_operator', 'scan_time'))]
mut_data  <- mut_data[ , (names(mut_data) %in% c('benchmark_name', 'program_name', 'mutation_operator', 'status', 'verification_time', 'mut_time', 'scan_time'))]

# Merge data by benchmark_name, program_name, mutation_operator
df <- merge(scan_data, mut_data, by=c('benchmark_name', 'program_name', 'mutation_operator'))

# Compute runtime
df$'runtime' <- df$'mut_time' - df$'verification_time'
# Convert milliseconds to seconds
df$'runtime' <- df$'runtime' * 0.001
df$'mut_time' <- df$'mut_time' * 0.001

# -------- Overall mutant mutation time

OUTPUT_FILE_PATH <- paste0(OUTPUT_DIR_PATH, '/', 'distribution-overall-runtime-mutants-gen.pdf')

# Remove any existing output file and create a new one
unlink(OUTPUT_FILE_PATH)
pdf(file=OUTPUT_FILE_PATH, family='Helvetica', width=6, height=2)

# Compute mutant runtime per program
runtimes_df <- df %>%
  dplyr::group_by(benchmark_name, program_name) %>%
  dplyr::summarise(
    total = n(),
    runtimes = sum(runtime),
    time = runtimes / total
  )

print(summary(runtimes_df$'time'))
print(runtimes_df[runtimes_df$'time' == min(runtimes_df$'time'), ])

# Calculate mean, median, and max runtimes
mean_time   <- mean(runtimes_df$'time')
median_time <- median(runtimes_df$'time')
max_time    <- max(runtimes_df$'time')

p <- ggplot(runtimes_df, aes(y=time)) + geom_boxplot()
# Horizontal box plot
p <- p + coord_flip()
# Scale y-axis
p <- p + scale_y_log10(
  breaks=scales::log_breaks(base=10, n=12),
  labels=scales::label_comma()
)
# Set labs
p <- p + labs(x='', y='Mutant generation runtime (seconds, log10 scale)')
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

# -------- Overall mutant total time

OUTPUT_FILE_PATH <- paste0(OUTPUT_DIR_PATH, '/', 'distribution-overall-runtime-mutants-total.pdf')

# Remove any existing output file and create a new one
unlink(OUTPUT_FILE_PATH)
pdf(file=OUTPUT_FILE_PATH, family='Helvetica', width=6, height=2)

total_mut_times_df <- df %>%
  dplyr::group_by(benchmark_name, program_name) %>%
  dplyr::summarise(
    total = n(),
    runtimes = sum(mut_time),
    time = runtimes / total
  )

print(summary(total_mut_times_df$'time'))
print(total_mut_times_df[total_mut_times_df$'time' == min(total_mut_times_df$'time'), ])

# Calculate mean, median, and max runtimes
mean_time   <- mean(total_mut_times_df$'time')
median_time <- median(total_mut_times_df$'time')
max_time    <- max(total_mut_times_df$'time')

p <- ggplot(total_mut_times_df, aes(y=time)) + geom_boxplot()
# Horizontal box plot
p <- p + coord_flip()
# Scale y-axis
p <- p + scale_y_log10(
  breaks=scales::log_breaks(base=10, n=12),
  labels=scales::label_comma()
)
# Set labs
p <- p + labs(x='', y='Mutant total runtime (seconds, log10 scale)')
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

# -------- Combined

OUTPUT_FILE_PATH <- paste0(OUTPUT_DIR_PATH, '/', 'distribution-overall-runtime-mutants-combined.pdf')

# Remove any existing output file and create a new one
unlink(OUTPUT_FILE_PATH)
pdf(file=OUTPUT_FILE_PATH, family='Helvetica', width=6, height=4)

# Prepare the data for combined plot
combined_df <- bind_rows(
  runtimes_df %>% mutate(type = "Mutant generation"),
  total_mut_times_df %>% mutate(type = "Mutant total")
)

# Calculate global min and max for consistent scaling
global_min <- min(min(runtimes_df$time), min(total_mut_times_df$time))
global_max <- max(max(runtimes_df$time), max(total_mut_times_df$time))

# Create combined plot
p <- ggplot(combined_df, aes(x = type, y = time, fill = type)) + 
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
    fill = 'Runtime type'
  ) +
  theme(
    axis.title.y = element_blank(),
    axis.text.y = element_blank(),
    axis.ticks.y = element_blank(),
    legend.position = "bottom"
  ) +
  scale_fill_manual(values = c("Mutant generation" = "cornflowerblue", "Mutant total" = "goldenrod"))

# Calculate statistics for annotation
gen_stats <- runtimes_df$time
total_stats <- total_mut_times_df$time

# Add text annotations
p <- p + annotate('text', x = Inf, y = Inf, hjust = 1, vjust = 1,
           label = paste0(
             'Generation Time\n',
             'Median = ', sprintf('%.2f', round(median(gen_stats), 2)), '\n',
             'Mean = ', sprintf('%.2f', round(mean(gen_stats), 2)), '\n',
             'Max = ', sprintf('%.2f', round(max(gen_stats), 2)), '\n',
             '\n',
             'Total Time\n',
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

# -------- Overall program mutation time

OUTPUT_FILE_PATH <- paste0(OUTPUT_DIR_PATH, '/', 'distribution-overall-runtime-programs-gen.pdf')

# Remove any existing output file and create a new one
unlink(OUTPUT_FILE_PATH)
pdf(file=OUTPUT_FILE_PATH, family='Helvetica', width=6, height=2)

# Compute average scan_time per program
scan_times_df <- df %>%
  dplyr::group_by(benchmark_name, program_name) %>%
  dplyr::summarise(
    total = n(),
    scan_times = sum(scan_time),
    scan_time = scan_times / total * 0.001
  )

# Compute total runtime per program
total_gen_times_df <- df %>%
  dplyr::group_by(benchmark_name, program_name) %>%
  dplyr::summarise(
    total_mut_time = sum(runtime)
  ) %>%
  # Join with scan_times
  dplyr::left_join(scan_times_df %>% select(benchmark_name, program_name, scan_time), 
                  by = c("benchmark_name", "program_name")) %>%
  # Calculate total runtime
  dplyr::mutate(
    total_runtime = total_mut_time + scan_time
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
# Scale y-axis
p <- p + scale_y_log10(
  breaks=scales::log_breaks(base=10, n=12),
  labels=scales::label_comma()
)
# Set labs
p <- p + labs(x='', y='Program mutants generation runtime (seconds, log10 scale)')
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

# -------- Overall program total time

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
  # Join with scan_times
  dplyr::left_join(scan_times_df %>% select(benchmark_name, program_name, scan_time), 
                  by = c("benchmark_name", "program_name")) %>%
  # Calculate total runtime
  dplyr::mutate(
    total_runtime = total_mut_time + scan_time
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
p <- p + labs(x='', y='Program total runtime (seconds, log10 scale)')
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

# -------- Combined

OUTPUT_FILE_PATH <- paste0(OUTPUT_DIR_PATH, '/', 'distribution-overall-runtime-programs-combined.pdf')

# Remove any existing output file and create a new one
unlink(OUTPUT_FILE_PATH)
pdf(file=OUTPUT_FILE_PATH, family='Helvetica', width=6, height=4)

# Prepare the data for combined plot
combined_df <- bind_rows(
  total_gen_times_df %>% mutate(type = "Program mutant generation"),
  total_times_df %>% mutate(type = "Program total")
)

# Calculate global min and max for consistent scaling
global_min <- min(min(total_gen_times_df$total_runtime), min(total_times_df$total_runtime))
global_max <- max(max(total_gen_times_df$total_runtime), max(total_times_df$total_runtime))

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
    fill = 'Runtime type'
  ) +
  theme(
    axis.title.y = element_blank(),
    axis.text.y = element_blank(),
    axis.ticks.y = element_blank(),
    legend.position = "bottom"
  ) +
  scale_fill_manual(values = c("Program mutant generation" = "cornflowerblue", "Program total" = "goldenrod"))

# Calculate statistics for annotation
gen_stats <- total_gen_times_df$total_runtime
total_stats <- total_times_df$total_runtime

# Add text annotations
p <- p + annotate('text', x = Inf, y = Inf, hjust = 1, vjust = 1,
           label = paste0(
             'Generation Time\n',
             'Median = ', sprintf('%.2f', round(median(gen_stats), 2)), '\n',
             'Mean = ', sprintf('%.2f', round(mean(gen_stats), 2)), '\n',
             'Max = ', sprintf('%.2f', round(max(gen_stats), 2)), '\n',
             '\n',
             'Total Time\n',
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

# -------- Mutant generation time per mutation operator

OUTPUT_FILE_PATH <- paste0(OUTPUT_DIR_PATH, '/', 'distribution-runtime-mutants-gen.pdf')

# Remove any existing output file and create a new one
unlink(OUTPUT_FILE_PATH)
pdf(file=OUTPUT_FILE_PATH, family='Helvetica', width=8, height=8)

# Calculate mean, median, and max number of runtime
mean_runtimes   <- mean(df$'runtime')
median_runtimes <- median(df$'runtime')
max_runtimes    <- max(df$'runtime')

# Distribution of runtime per mutation operator
p <- ggplot(df, aes(x=mutation_operator, y=runtime)) + geom_boxplot() #+ facet_wrap(~ benchmark_name, scales='free_y')
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
p <- p + labs(x='Mutation Operator', y='Mutant generation runtime (seconds, log10 scale)')
# Print plot
print(p)

# Close output file
dev.off()
# Embed fonts
embed_fonts_in_a_pdf(OUTPUT_FILE_PATH)

# -------- Mutant total time per mutation operator

OUTPUT_FILE_PATH <- paste0(OUTPUT_DIR_PATH, '/', 'distribution-runtime-mutants-total.pdf')

# Remove any existing output file and create a new one
unlink(OUTPUT_FILE_PATH)
pdf(file=OUTPUT_FILE_PATH, family='Helvetica', width=8, height=8)

# Calculate mean, median, and max number of runtime
mean_runtimes   <- mean(df$'mut_time')
median_runtimes <- median(df$'mut_time')
max_runtimes    <- max(df$'mut_time')

# Distribution of mut_time per mutation operator
p <- ggplot(df, aes(x=mutation_operator, y=mut_time)) + geom_boxplot() #+ facet_wrap(~ benchmark_name, scales='free_y')
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
p <- p + labs(x='Mutation Operator', y='Mutant total runtime (seconds, log10 scale)')
# Print plot
print(p)

# Close output file
dev.off()
# Embed fonts
embed_fonts_in_a_pdf(OUTPUT_FILE_PATH)

# EOF
