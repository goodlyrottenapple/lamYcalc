SHELL=bash

default: all

all:
	pandoc *.md --highlight-style=pygments --latex-engine=xelatex --bibliography=../ref.bib  -V papersize:"a4paper" -V geometry:margin=1in -o out.pdf