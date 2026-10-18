MAIN := main-human
LATEXMK := latexmk
BUILD_INFO := ../build-info.tex

.PHONY: all clean distclean

all: $(MAIN).pdf

BLOCKS := $(wildcard blocks/*.tex)

$(MAIN).pdf: $(MAIN).tex $(BLOCKS) ../abstract.tex ../references.bib \
		../provenance-footer.tex $(BUILD_INFO)
	$(LATEXMK) -pdf -interaction=nonstopmode -halt-on-error $(MAIN).tex

.PHONY: force-build-info
force-build-info:

$(BUILD_INFO): force-build-info
	@commit="$$(git rev-parse --short=12 HEAD 2>/dev/null || printf unknown)"; \
	state="$$(test -z "$$(git status --porcelain --untracked-files=normal 2>/dev/null)" && printf clean || printf dirty)"; \
	timestamp="$$(TZ=America/Edmonton date '+%Y-%m-%d %H:%M:%S %Z')"; \
	printf '\\renewcommand{\\buildmetadata}{git %s \\textbar{} %s \\textbar{} compiled %s}\n' \
	  "$$commit" "$$state" "$$timestamp" > $(BUILD_INFO)

clean:
	$(LATEXMK) -c $(MAIN).tex

distclean:
	$(LATEXMK) -C $(MAIN).tex
