OTTNAME=lang

main.pdf: main.tex
	latexmk $<

%.tex: %.otex $(OTTNAME).ott
	@rm -rf $@
	ott -i $(OTTNAME).ott -tex_filter $< $@
	@chmod -w $@
