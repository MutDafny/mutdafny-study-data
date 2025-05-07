# ------------------------------------------------------------------------------
# A set of util functions for the data analysis.
# ------------------------------------------------------------------------------

# -------------------------------------------------------------------------- Env

set.seed(1)

script_path <- function() {
  # this code only works if `utils.R` is 'source'd, for a more comprehensive
  # version of this function visit https://stackoverflow.com/a/15373917/998816
  return(normalizePath(sys.frames()[[1]]$ofile))
}

script_dir_path <- function() {
  return(dirname(script_path()))
}

platform      <- R.Version()$'platform'
version       <- paste(R.Version()[c('major', 'minor')], collapse='.')
local_library <- paste(script_dir_path(), '/../../.third-parties/R/', platform, '-library/', version, sep='')
if (!file.exists(local_library)) {
  dir.create(local_library, showWarnings=TRUE, recursive=TRUE)
}

# --------------------------------------------------------------------- Wrappers

'%!in%' <- function(x,y)!('%in%'(x,y)) # Wrapper to 'not in'

load_library <- function(library_name) {
  library(library_name, lib.loc=local_library)
}

load_CSV <- function(csv_path) {
  return (read.csv(csv_path, header=TRUE, stringsAsFactors=FALSE))
}

load_TABLE <- function(zip_path) {
  return(read.table(gzfile(zip_path), header=TRUE, stringsAsFactors=FALSE))
}

#
# Replaces all NaNs in a dataframe with 0
#
is.nan.data.frame <- function(df) {
  do.call(cbind, lapply(df, is.nan))
}

replace_string <- function(string, find, replace) {
  gsub(find, replace, string)
}

#
# Wrapper function for the official embed_fonts function.
#
set_fonts <- function(filename) {
  library('extrafont') # install.packages('extrafont')
  embed_fonts(filename, options="-dSubsetFonts=true -dEmbedAllFonts=true -dCompatibilityLevel=1.4 -dPDFSETTINGS=/prepress -dMaxSubsetPct=100")
}

#
# Plots the provided text on a dedicated page.  This function is usually used to
# separate plots for multiple analyses in the same PDF.
#
plot_label <- function(text) {
  library('ggplot2') # install.packages('ggplot2')
  p <- ggplot() + annotate('text', label=text, x=4, y=25, size=8) + theme_void()
  print(p)
}

# ---------------------------------------------------------------- Study related

# TODO

# EOF
