OTTNAME=lang

main.pdf: main.tex
	latexmk $<

%.tex: %.otex $(OTTNAME).ott
	@rm -rf $@
	ott -i $(OTTNAME).ott -o lang.tex -tex_wrap false -tex_filter $< $@
	@chmod -w $@
