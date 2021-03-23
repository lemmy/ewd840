






## OUTDATED, PLEASE OPEN README.Rmd INSTEAD!






## here package promises to magically find your csv files, hooray!
#install.packages("here")
#library(here)
#data <- read.csv(header=TRUE, sep = "#", file = here("N007.csv"))

## If here's magic fails, this is how to make read.csv find the given
## file at its location and separator into 'data'.
setwd("~/src/TLA/_specs/models/tutorials/ewd840/")
data <- read.csv(header=TRUE, sep = "#", file = 'N007.csv')

## dplyr lets us group 'data' based on the 'Variant' column.
## Based on this grouping, we calculate mean, sd, and variance
## for 'data'.
library(dplyr)
by_variant <- group_by(data,Variant)
summary = summarise(by_variant,
                    mean_length = mean(Length),
                    var_length = var(Length),
                    sd_length = sd(Length),
                    mean(InitiateProbe),
                    mean(SendMsg),
                    mean(PassToken),
                    mean(Deactivate),
                    N = mean(Node)
)
summary

## Plot a histogram of the mean_length (ordered by increasing length of behaviors).
library(ggplot2)
ggplot(summary, 
  aes(x = reorder(Variant, mean_length), y = mean_length, fill = Variant)) +
  geom_bar(stat = "identity") +
  geom_errorbar(aes(ymin=mean_length-sd_length, ymax=mean_length+sd_length), width=.2,
                position=position_dodge(.9)) +
  theme_minimal() +
  labs(
    x = "Spec variant",
    y = "Average length of behaviors",
    title = paste(
      "Number of Nodes:", data[,7][1], "Traces:", nrow(data)
  )
)

##
library(ggplot2)
ggplot(data = data, mapping = aes(x=Length)) + 
  geom_histogram(aes(y=..density..),fill="bisque",color="white",alpha=0.9) + 
  geom_density() +
  geom_rug() +
  labs(x='Trace Length') +
  theme_minimal()

ggplot(data = data, mapping = aes(x=SendMsg)) + 
  geom_histogram(aes(y=..density..),fill="bisque",color="white",alpha=0.9) + 
  geom_density() +
  geom_rug() +
  labs(x='SendMsg') +
  theme_minimal()


##install.packages("scatterplot3d")
library(scatterplot3d)
scatterplot3d(
  data[,2:4], pch = 19, color = "steelblue",
  grid = TRUE, box = FALSE
  # , mar = c(3, 3, 0.5, 3)        
)

##install.packages("GGally")
library(GGally)
library(ggplot2)
ggpairs(data)

##install.packages("ggcorrplot")
library("ggcorrplot")
my_data <- data[, c("Length", "SendMsg", "InitiateProbe", "PassToken", "Deactivate")] # c(2,3,4)
p.mat <- cor_pmat(my_data)

## Check for correlation in 'data'
## 'spearman' (3) correlation because data has no normal distribution
## (see previous plots).
corr <- round(cor(my_data), 3)

ggcorrplot(corr, p.mat = cor_pmat(my_data),
           hc.order = TRUE, type = "lower",
           color = c("#FC4E07", "white", "#00AFBB"),
           outline.col = "white", lab = TRUE)
