#!/usr/bin/env Rscript
args <- commandArgs(trailingOnly = TRUE)

data <- read.csv(header = TRUE, sep = ",", file = args[1])
samples <- nrow(data)

svg(gsub(".csv$", ".svg", args[1]))

layout(matrix(c(1,1,2,3), 2, 2, byrow = TRUE),
       widths=c(3,1), heights=c(1,2))

barplot(table(data$p), main = paste("Knuth Yao -", samples, "samples"), xlab = "p",col="orange")
barplot(table(data$side), xlab = "Side")
barplot(table(data$flip), xlab = "H/T",col="darkgreen")
