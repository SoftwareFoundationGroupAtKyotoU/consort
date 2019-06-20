.PHONY: all src/all clean

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

clean:
	make -C src/ clean
	latexmk -f -C main.tex
	@rm -rf main.tex
