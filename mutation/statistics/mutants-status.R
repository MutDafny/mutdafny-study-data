# ------------------------------------------------------------------------------
# This script computes and print as a latex table the number of generated mutants,
# the number of killed, survived, invalid, and timeout mutants per mutation
# operator.
#
# Usage:
# Rscript mutants-status.R
#   <mutation data file path, e.g., ../data/generated/mut-data.csv>
#   <output dir path, e.g., ../data/generated>
# ------------------------------------------------------------------------------

source('../../utils/statistics/utils.R')
library('dplyr', lib.loc=local_library)
library('ggplot2', lib.loc=local_library)
library('ggbeeswarm', lib.loc=local_library)

# ------------------------------------------------------------------------- Args

args = commandArgs(trailingOnly=TRUE)
if (length(args) != 2) {
  stop('USAGE: Rscript mutants-gen.R <mutation data file path, e.g., ../data/generated/mut-data.csv> <output dir path, e.g., ../data/generated>')
}

# Args
DATA_FILE_PATH  <- args[1] # benchmark_name,program_name,mutation_position,mutation_operator,mutation,status,parsing_time,plugin_time,resolution_time,verification_time,run_time
OUTPUT_DIR_PATH <- args[2]

# ------------------------------------------------------------------------- Main

# Load data
df <- load_CSV(DATA_FILE_PATH)

OUTPUT_FILE_PATH <- paste0(OUTPUT_DIR_PATH, '/', 'distribution-status-mutants.tex')

# Remove any existing output file and create a new one
unlink(OUTPUT_FILE_PATH)
sink(OUTPUT_FILE_PATH, append=FALSE, split=TRUE)

# Columns
cat('\\begin{tabular}{@{}lrrrrr@{}} \\toprule', '\n', sep='')
# Header
cat('\\textbf{Operator} & \\textbf{\\# Mutants} & \\textbf{\\# Killed} & \\textbf{\\# Survived} & \\textbf{\\# Invalid} & \\textbf{\\# Timeout}', ' \\\\ \\midrule', '\n', sep='')
# Body
for (operator in (sort(unique(df$'mutation_operator')))) {
  operator_mutants <- df[df$'mutation_operator' == operator, ]
  cat(operator)

  num_mutants <- nrow(operator_mutants)
  cat(' & ', format(num_mutants, scientific=FALSE, big.mark=',', small.mark=','), sep='')

  num_killed <- nrow(operator_mutants[operator_mutants$'status' == 'killed', ])
  per_killed <- num_killed / num_mutants * 100.0
  cat(' & ', format(num_killed, scientific=FALSE, big.mark=',', small.mark=','), ' (', sprintf('%.2f', round(per_killed, 2)), '\\%)', sep='')

  num_survived <- nrow(operator_mutants[operator_mutants$'status' == 'survived', ])
  per_survived <- num_survived / num_mutants * 100.0
  cat(' & ', format(num_survived, scientific=FALSE, big.mark=',', small.mark=','), ' (', sprintf('%.2f', round(per_survived, 2)), '\\%)', sep='')

  num_invalid <- nrow(operator_mutants[operator_mutants$'status' == 'invalid', ])
  per_invalid <- num_invalid / num_mutants * 100.0
  cat(' & ', format(num_invalid, scientific=FALSE, big.mark=',', small.mark=','), ' (', sprintf('%.2f', round(per_invalid, 2)), '\\%)', sep='')

  num_timeout <- nrow(operator_mutants[operator_mutants$'status' == 'timeout', ])
  per_timeout <- num_timeout / num_mutants * 100.0
  cat(' & ', format(num_timeout, scientific=FALSE, big.mark=',', small.mark=','), ' (', sprintf('%.2f', round(per_timeout, 2)), '\\%)', sep='')

  cat(' \\\\', '\n', sep='')
}
cat('\\midrule', '\n', sep='')
cat('\\textit{Total}')

num_mutants <- nrow(df)
cat(' & ', format(num_mutants, scientific=FALSE, big.mark=',', small.mark=','), sep='')

num_killed <- nrow(df[df$'status' == 'killed', ])
per_killed <- num_killed / num_mutants * 100.0
cat(' & ', format(num_killed, scientific=FALSE, big.mark=',', small.mark=','), ' (', sprintf('%.2f', round(per_killed, 2)), '\\%)', sep='')

num_survived <- nrow(df[df$'status' == 'survived', ])
per_survived <- num_survived / num_mutants * 100.0
cat(' & ', format(num_survived, scientific=FALSE, big.mark=',', small.mark=','), ' (', sprintf('%.2f', round(per_survived, 2)), '\\%)', sep='')

num_invalid <- nrow(df[df$'status' == 'invalid', ])
per_invalid <- num_invalid / num_mutants * 100.0
cat(' & ', format(num_invalid, scientific=FALSE, big.mark=',', small.mark=','), ' (', sprintf('%.2f', round(per_invalid, 2)), '\\%)', sep='')

num_timeout <- nrow(df[df$'status' == 'timeout', ])
per_timeout <- num_timeout / num_mutants * 100.0
cat(' & ', format(num_timeout, scientific=FALSE, big.mark=',', small.mark=','), ' (', sprintf('%.2f', round(per_timeout, 2)), '\\%)', sep='')

cat(' \\\\', '\n', sep='')

cat('\\bottomrule', '\n', sep='')
cat('\\end{tabular}', '\n', sep='')
sink()

# --------

OUTPUT_FILE_PATH <- paste0(OUTPUT_DIR_PATH, '/', 'distribution-overall-mutation-score.pdf')

# Remove any existing output file and create a new one
unlink(OUTPUT_FILE_PATH)
pdf(file=OUTPUT_FILE_PATH, family='Helvetica', width=6, height=2)

# Compute kill ratio per program
kill_ratios <- df %>%
  dplyr::group_by(benchmark_name, program_name) %>%
  dplyr::summarise(
    total = n(),
    killed = sum(status == 'killed'),
    score = killed / total * 100.0
  )

# Calculate mean, median, and max mutation score
mean_score   <- mean(kill_ratios$'score')
median_score <- median(kill_ratios$'score')

print(summary(kill_ratios$'score'))
print(kill_ratios[kill_ratios$'score' == min(kill_ratios$'score'), ])
print(kill_ratios[kill_ratios$'score' >= mean_score, ])
print(kill_ratios[kill_ratios$'score' == 100, ])

p <- ggplot(kill_ratios, aes(y=score)) + geom_boxplot()
# Horizontal box plot
p <- p + coord_flip()
# Set labs
p <- p + labs(x='', y='% Mutation Score') +
  scale_y_continuous(breaks=seq(from=0, to=100, by=10))
# Remove axis
p <- p + theme(axis.title.y = element_blank(), axis.text.y = element_blank(), axis.ticks.y = element_blank())
# Add text values
p <- p + annotate('text', x=Inf, y=0, hjust=0, vjust=1.5,
           label=paste0(#
             'Median = ', sprintf('%.2f', round(median_score, 2)), '%', '\n',
             'Mean = ', sprintf('%.2f', round(mean_score, 2)), '%'),
           size=4, color='black')
# Print plot
print(p)

# Close output file
dev.off()
# Embed fonts
embed_fonts_in_a_pdf(OUTPUT_FILE_PATH)

# --------

OUTPUT_FILE_PATH <- paste0(OUTPUT_DIR_PATH, '/', 'distribution-mutation-score-per-mutation-operator.pdf')

# Remove any existing output file and create a new one
unlink(OUTPUT_FILE_PATH)
pdf(file=OUTPUT_FILE_PATH, family='Helvetica', width=8, height=8)

# Compute kill ratio per program and operator
kill_ratios <- df %>%
  dplyr::group_by(benchmark_name, program_name, mutation_operator) %>%
  dplyr::summarise(
    total = n(),
    killed = sum(status == 'killed'),
    score = killed / total * 100.0
  )

print(summary(kill_ratios$'score'))
print(kill_ratios[kill_ratios$'score' == min(kill_ratios$'score'), ])

# Calculate mean, median, and max mutation score
mean_score   <- mean(kill_ratios$'score')
median_score <- median(kill_ratios$'score')
max_score    <- max(kill_ratios$'score')

p <- ggplot(kill_ratios, aes(x=mutation_operator, y=score)) + geom_boxplot(outlier.shape=NA) #+ facet_wrap(~ benchmark_name, scales='free_y')
# Spreads points nicely without as much overlap
p <- p + geom_quasirandom(alpha=0.2, size=0.7)
# Add horizontal line for mean number of mutants
p <- p + geom_hline(yintercept=mean_score, linetype='dashed', color='brown')
# Add text label to the line, anchored at first bin (leftmost)
p <- p + annotate('text', x=0, y=mean_score, vjust=-0.5, hjust=0,
           label=paste0('Mean = ', sprintf('%.2f', round(mean_score, 2))),
           size=4, color='brown')
# Add horizontal line for median number of mutants
p <- p + geom_hline(yintercept=median_score, linetype='dashed', color='blue')
# Add text label to the line, anchored at first bin (leftmost)
p <- p + annotate('text', x=0, y=median_score, vjust=-0.5, hjust=0,
           label=paste0('Median = ', sprintf('%.2f', round(median_score, 2))),
           size=4, color='blue')
# Add horizontal line for max number of mutants
p <- p + geom_hline(yintercept=max_score, linetype='dashed', color='red')
# Add text label to the line, anchored at first bin (leftmost)
p <- p + annotate('text', x=8, y=max_score, vjust=-0.5, hjust=0,
           label=paste0('Max = ', sprintf('%.2f', round(max_score, 2))),
           size=4, color='red')
# Set labs
p <- p + labs(x='Mutation Operator', y='Ratio Killed Mutants') +
  scale_y_continuous(breaks=seq(from=0, to=100, by=10))
# Print plot
print(p)

# Close output file
dev.off()
# Embed fonts
embed_fonts_in_a_pdf(OUTPUT_FILE_PATH)

# EOF
