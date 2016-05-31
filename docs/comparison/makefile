SHELL=bash
NIX_LINK=$(HOME)/.nix-profile
export PATH := $(NIX_LINK)/bin:$(NIX_LINK)/sbin:$(PATH)

default: all

all:
	pandoc *.md --highlight-style=tango --latex-engine=xelatex --variable monofont="FreeMono" --bibliography=../ref.bib -V papersize:"a4paper" -V geometry:margin=1in -o out.pdf