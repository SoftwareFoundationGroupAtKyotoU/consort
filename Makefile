OTTNAME=lang

main.pdf: main.tex
	latexmk $<

$(OTTNAME).tex $(OTTNAME).sys: $(OTTNAME).ott
	ott -writesys $(OTTNAME).sys -tex_wrap false -o $(OTTNAME).tex -i $(OTTNAME).ott

%.tex: %.otex $(OTTNAME).tex $(OTTNAME).sys
	@rm -rf $@
	ott -readsys $(OTTNAME).sys -tex_filter $< $@
	@chmod -w $@
