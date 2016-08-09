basedir=$(PWD)

sources := $(filter-out proposal/prop.md,$(wildcard */*.md))
styledir=$(basedir)/style
scriptedir=$(basedir)/scripts

meta=$(basedir)/metadata.yaml

out_name=thesis



#  -- Bib Vars --------------------------------------------------------------
# the dir where all the citation styles are
bib_styles    = $(styledir)/citation_styles

# this is your .bib file
bibfile       = ref.bib

# common citation styles for CS
bib_acm_long  = $(bib_styles)/acm-sig-proceedings-long-author-list.csl
bib_acm_short = $(bib_styles)/acm-sig-proceedings.csl
bib_ieee      = $(bib_styles)/ieee-with-url.csl

# CHANGE: change this to use your custom citation style
bib_style     = $(bib_ieee)



define pandoc
	pandoc $(meta) \
	$(sources) \
	-o "$(1)" \
	--template="$(styledir)/template.tex" \
	--filter "$(scriptedir)/pandoc-amsthm.py" \
	--filter "$(scriptedir)/pandoc-minted.py" \
	--bibliography="$(bibfile)"  \
	--chapters \
	-N \
	--latex-engine=xelatex \
	$(2) 2>"$(basedir)"/pandoc.log
endef

default: all

all:
	@$(call pandoc,"$(out_name).tex")
	export PATH="$(basedir):$(styledir):($PATH)"
	xelatex -shell-escape "$(out_name).tex"

clean: 
	rm $(out_name).*
	rm -r _minted*