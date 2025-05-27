# ------------------------------------------------------------------------------
# This script computes and plots the distribution number of mutants per mutation
# operator.
#
# Usage:
# Rscript mutants.R
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
if (length(args) != 2) {
  stop('USAGE: Rscript mutants.R <mutation data file path, e.g., ../data/generated/mut-data.csv> <output dir path, e.g., ../data/generated>')
}

# Args
DATA_FILE_PATH  <- args[1] # benchmark_name,program_name,mutation_position,mutation_operator,mutation,status,parsing_time,plugin_time,resolution_time,verification_time,run_time
OUTPUT_DIR_PATH <- args[2]

# ------------------------------------------------------------------------- Main

# Load data
data <- load_CSV(DATA_FILE_PATH)

OUTPUT_FILE_PATH <- paste0(OUTPUT_DIR_PATH, '/', 'distribution-number-mutants-per-operator.pdf')

# Remove any existing output file and create a new one
unlink(OUTPUT_FILE_PATH)
pdf(file=OUTPUT_FILE_PATH, family='Helvetica', width=6, height=6)

# Count mutants per benchmark, program, and mutation_operator
mutant_counts <- data %>%
  dplyr::group_by(benchmark_name, program_name, mutation_operator) %>%
  dplyr::summarise(count = n(), .groups = 'drop')

# Calculate mean, median, and max number of mutants
mean_num_mutants   <- mean(mutant_counts$'count')
median_num_mutants <- median(mutant_counts$'count')
max_num_mutants    <- max(mutant_counts$'count')

# Distribution of mutant counts per mutation operator
p <- ggplot(mutant_counts, aes(x=mutation_operator, y=count)) + geom_boxplot(outlier.shape=NA) #+ facet_wrap(~ benchmark_name, scales='free_y')
# Spreads points nicely without as much overlap
p <- p + geom_quasirandom(alpha=0.2, size=0.7)
# Add horizontal line for mean number of mutants
p <- p + geom_hline(yintercept=mean_num_mutants, linetype='dashed', color='brown')
# Add text label to the line, anchored at first bin (leftmost)
p <- p + annotate('text', x=0, y=mean_num_mutants, vjust=-0.5, hjust=0,
           label=paste0('Mean = ', sprintf('%.2f', round(mean_num_mutants, 2))),
           size=4, color='brown')
# Add horizontal line for median number of mutants
p <- p + geom_hline(yintercept=median_num_mutants, linetype='dashed', color='blue')
# Add text label to the line, anchored at first bin (leftmost)
p <- p + annotate('text', x=0, y=median_num_mutants, vjust=-0.5, hjust=0,
           label=paste0('Median = ', sprintf('%.2f', round(median_num_mutants, 2))),
           size=4, color='blue')
# Add horizontal line for max number of mutants
p <- p + geom_hline(yintercept=max_num_mutants, linetype='dashed', color='red')
# Add text label to the line, anchored at first bin (leftmost)
p <- p + annotate('text', x=0, y=max_num_mutants, vjust=-0.5, hjust=0,
           label=paste0('Max = ', sprintf('%.2f', round(max_num_mutants, 2))),
           size=4, color='red')
# Scale y-axis
p <- p + scale_y_log10(
  breaks=scales::log_breaks(base=10, n=15),
  labels=scales::label_comma()
)
# Set labs
p <- p + labs(x='Mutation Operator', y='# Mutants (log10 scale)')
# Print plot
print(p)

# Close output file
dev.off()
# Embed fonts
embed_fonts_in_a_pdf(OUTPUT_FILE_PATH)

# EOF
