# ------------------------------------------------------------------------------
# This script computes and plots the distribution MutDafny's runtime at generating
# mutants.
#
# Usage:
#   Rscript mutants-gen.R
#     <scan data file path, e.g., ../data/generated/scan-data.csv>
#     <mutation data file path, e.g., ../data/generated/mut-data.csv>
#     <output dir path, e.g., ../data/generated>
# ------------------------------------------------------------------------------

source('../../utils/statistics/utils.R')
library('ggplot2')
library('ggbeeswarm')
library('scales')

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
df$'runtime' <- df$'scan_time' + df$'mut_time' - df$'verification_time'
# Convert milliseconds to seconds
df$'runtime' <- df$'runtime' * 0.001

OUTPUT_FILE_PATH <- paste0(OUTPUT_DIR_PATH, '/', 'distribution-runtime-mutants-gen.pdf')

# Remove any existing output file and create a new one
unlink(OUTPUT_FILE_PATH)
pdf(file=OUTPUT_FILE_PATH, family='Helvetica', width=6, height=6)

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
p <- p + labs(x='Mutation Operator', y='Runtime (seconds, log10 scale)')
# Print plot
print(p)

# Close output file
dev.off()
# Embed fonts
embed_fonts_in_a_pdf(OUTPUT_FILE_PATH)

# EOF
