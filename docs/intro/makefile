default: all

all:
	pandoc *.md --standalone --filter ../pandoc-minted.py --variable monofont="FreeMono" --bibliography=../ref.bib -V papersize:"a4paper" -V geometry:margin=1in -o out.tex
	xelatex -shell-escape out.tex

clean: 
	rm out.tex
	rm out.aux
	rm out.log
	rm out.out 
	rm -r _minted-out