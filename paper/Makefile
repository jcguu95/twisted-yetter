MAIN := main
LATEXMK := latexmk

.PHONY: all clean distclean

all: $(MAIN).pdf

$(MAIN).pdf: $(MAIN).tex abstract.tex introduction.tex untitled-section.tex references.bib
	$(LATEXMK) -pdf -interaction=nonstopmode -halt-on-error $(MAIN).tex

clean:
	$(LATEXMK) -c $(MAIN).tex

distclean:
	$(LATEXMK) -C $(MAIN).tex
