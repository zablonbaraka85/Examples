#!/usr/bin/env Rscript
args <- commandArgs(trailingOnly = TRUE)

data <- read.csv(header = TRUE, sep = ",", file = args[1])
samples <- nrow(data)
data <- table(data)

svg(gsub(".csv$", ".svg", args[1]))
barplot(data, main = paste("Knuth Yao -", samples, "samples"), xlab = "Side")
