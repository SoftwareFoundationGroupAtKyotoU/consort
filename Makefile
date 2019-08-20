.PHONY: all src/all clean

OTTNAME=lang
TEX=intro.tex preliminaries.tex typesystem.tex appendix.tex	\
	related_work.tex impl.tex experiments.tex conclusion.tex semantics.tex

all: main.pdf src/all

main.pdf: main.tex $(TEX)
	latexmk $<

%.tex: %.otex $(OTTNAME).ott
	@rm -rf $@
	ott -i $(OTTNAME).ott -o lang.tex -tex_wrap false
	ott -i $(OTTNAME).ott -tex_wrap false -tex_filter $< $@
	@chmod -w $@

src/all:
	make -C src all

clean:
	make -C src/ clean
	latexmk -f -C main.tex
	@rm -rf main.tex $(TEX)
