MAIN := main
LATEXMK := latexmk
BUILD_INFO := build-info.tex

.PHONY: all clean distclean

all: $(MAIN).pdf

$(MAIN).pdf: $(MAIN).tex abstract.tex contents.tex introduction.tex preliminaries.tex \
		preliminaries/fusion-categories.tex preliminaries/topology-input.tex \
		preliminaries/low-dimensional-topology.tex evaluator.tex \
		evaluator/graphical-construction.tex evaluator/kirby-invariance.tex \
		evaluator/untwisted-comparison.tex stable-calculation.tex \
		stable-calculation/connected-sums.tex \
		stable-calculation/premodular-formulas.tex \
		stable-calculation/modular-specialization.tex \
		stable-calculation/modular-examples.tex future-directions.tex \
		appendix.tex appendix/numerical-checks.tex \
		appendix/computational-cost.tex \
		references.tex references.bib $(BUILD_INFO)
	$(LATEXMK) -pdf -interaction=nonstopmode -halt-on-error $(MAIN).tex

.PHONY: force-build-info
force-build-info:

$(BUILD_INFO): force-build-info
	@commit="$$(git rev-parse --short=12 HEAD 2>/dev/null || printf unknown)"; \
	state="$$(git diff --quiet --ignore-submodules HEAD -- 2>/dev/null && printf clean || printf dirty)"; \
	timestamp="$$(TZ=America/Edmonton date '+%Y-%m-%d %H:%M:%S %Z')"; \
	printf '\\renewcommand{\\buildmetadata}{Compiled %s; commit %s (%s).}\n' \
	  "$$timestamp" "$$commit" "$$state" > $(BUILD_INFO)

clean:
	$(LATEXMK) -c $(MAIN).tex

distclean:
	$(LATEXMK) -C $(MAIN).tex
	rm -f $(BUILD_INFO)
