SHELL=bash

default: all

all:
	pandoc *.md --latex-engine=xelatex --bibliography=ref.bib -V papersize:"a4paper" -V geometry:margin=1in -o prop.pdf