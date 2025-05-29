args = commandArgs(trailingOnly=TRUE)
if (length(args) != 1) {
  stop('USAGE: get-libraries.R <path>')
}

PATH <- args[1]

# Load utils file
source(paste(PATH, '/../utils/statistics/utils.R', sep=''))
# R repository
repository <- 'https://cloud.r-project.org'

# Install and load packages (aka runtime sanity check)
install.packages('data.table', lib=local_library, repos=repository)
library('data.table', lib.loc=local_library)
install.packages('dplyr', lib=local_library, repos=repository)
library('dplyr', lib.loc=local_library)
install.packages('stringr', lib=local_library, repos=repository)
library('stringr', lib.loc=local_library)
install.packages('extrafont', lib=local_library, repos=repository)
library('extrafont', lib.loc=local_library)
install.packages('farver', lib=local_library, repos=repository)
library('farver', lib.loc=local_library)
install.packages('RColorBrewer', lib=local_library, repos=repository)
library('RColorBrewer', lib.loc=local_library)
install.packages('withr', lib=local_library, repos=repository)
library('withr', lib.loc=local_library)
install.packages('utf8', lib=local_library, repos=repository)
library('utf8', lib.loc=local_library)
install.packages('labeling', lib=local_library, repos=repository)
library('labeling', lib.loc=local_library)
install.packages('ggplot2', lib=local_library, repos=repository) # required by caret
library('ggplot2', lib.loc=local_library)
install.packages('ggbeeswarm', lib=local_library, repos=repository)
library('ggbeeswarm', lib.loc=local_library)
install.packages('scales', lib=local_library, repos=repository)
library('scales', lib.loc=local_library)
# Exit
quit(save='no', status=0)

# EOF
