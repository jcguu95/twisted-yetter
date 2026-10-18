MAIN := main-human
LATEXMK := latexmk

.PHONY: all clean distclean

all: $(MAIN).pdf

BLOCKS := $(wildcard blocks/*.tex)

$(MAIN).pdf: $(MAIN).tex $(BLOCKS) ../abstract.tex ../references.bib
	$(LATEXMK) -pdf -interaction=nonstopmode -halt-on-error $(MAIN).tex

clean:
	$(LATEXMK) -c $(MAIN).tex

distclean:
	$(LATEXMK) -C $(MAIN).tex
