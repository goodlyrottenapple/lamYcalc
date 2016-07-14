basedir=$(PWD)
styledir=$(basedir)/../style

remove := $(wildcard out.*)

default: all

all:
	cd .. && $(MAKE)

clean: 
	rm $(remove)
	rm -r _minted-*