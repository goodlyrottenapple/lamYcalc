remove := $(filter-out out.pdf,$(wildcard out.*))

default: all

all:
	pandoc ../metadata.yaml *.md --standalone --filter ../pandoc-minted.py --variable monofont="FreeMono" --bibliography=../ref.bib -V papersize:"a4paper" -V geometry:margin=1in -o out.tex
	xelatex -shell-escape out.tex

clean: 
	rm $(remove)
	rm -r _minted-out