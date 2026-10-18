MAIN := main
LATEXMK := latexmk

.PHONY: all clean distclean

all: $(MAIN).pdf

$(MAIN).pdf: $(MAIN).tex preliminaries.tex kirby-presentations.tex evaluator.tex \
		invariance.tex stable-calculation.tex future-directions.tex \
		computational-evidence.tex
	$(LATEXMK) -pdf -interaction=nonstopmode -halt-on-error $(MAIN).tex

clean:
	$(LATEXMK) -c $(MAIN).tex

distclean:
	$(LATEXMK) -C $(MAIN).tex
