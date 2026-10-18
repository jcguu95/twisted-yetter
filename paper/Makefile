MAIN := main
LATEXMK := latexmk
BUILD_INFO := build-info.tex
FIGURE_GALLERY := figures/gallery
HUMAN_BLOCKS := $(wildcard human/blocks/*.tex)
FIGURE_SOURCES := figures/styles.tex \
	figures/01-kirby-cancelling-pair.tex \
	figures/02-special-kirby-representative.tex \
	figures/03-dotted-cocore-chart.tex \
	figures/04-cut-open-boundary-word.tex \
	figures/05-unit-projector-in-context.tex \
	figures/06-kirby-colour-character.tex \
	figures/07-two-over-two-movie.tex \
	figures/08-two-over-one-after-cutting.tex \
	figures/09-one-over-one-after-cutting.tex \
	figures/10-cancellation-normal-forms.tex

.PHONY: all figures clean distclean

all: $(MAIN).pdf

figures: $(FIGURE_GALLERY).pdf

$(FIGURE_GALLERY).pdf: $(FIGURE_GALLERY).tex $(FIGURE_SOURCES)
	$(LATEXMK) -cd -pdf -interaction=nonstopmode -halt-on-error $(FIGURE_GALLERY).tex

$(MAIN).pdf: $(MAIN).tex abstract.tex contents.tex introduction.tex preliminaries.tex \
		preliminaries/fusion-categories.tex preliminaries/topology-input.tex \
		preliminaries/low-dimensional-topology.tex evaluator.tex \
		kirby-presentations.tex invariance.tex \
		evaluator/graphical-construction.tex evaluator/kirby-invariance.tex \
		evaluator/untwisted-comparison.tex stable-calculation.tex \
		stable-calculation/connected-sums.tex \
		stable-calculation/premodular-formulas.tex \
		stable-calculation/modular-specialization.tex \
		stable-calculation/modular-examples.tex future-directions.tex \
		appendix.tex appendix/numerical-checks.tex \
		appendix/computational-cost.tex \
		appendix/formalization-interface.tex \
		references.tex references.bib $(HUMAN_BLOCKS) $(BUILD_INFO)
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
