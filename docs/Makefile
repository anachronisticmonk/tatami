# Build the design documents. `make` builds everything, `make phase_1` one of them.
#
# Each document is a directory holding one or more top-level .tex files. Add a
# directory to DOCS and a rule below and it builds with the rest.

LATEXMK := latexmk -pdf -interaction=nonstopmode -halt-on-error

DOCS := phase_1

.PHONY: all clean $(DOCS)

all: $(DOCS)

phase_1:
	cd phase_1 && $(LATEXMK) lowering.tex

clean:
	cd phase_1 && latexmk -C
