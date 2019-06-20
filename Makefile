.PHONY: all src/all

OTTNAME=lang

all: main.pdf src/all

main.pdf: main.tex
	latexmk $<

%.tex: %.otex $(OTTNAME).ott
	@rm -rf $@
	ott -i $(OTTNAME).ott -tex_filter $< $@
	@chmod -w $@

src/all:
	make -C src all
