# Build the design documents. `make` builds everything, `make phase_1` one of them.
#
# Each document is a directory holding one top-level .tex named after nothing in
# particular; add a directory here and to DOCS and it builds with the rest.

LATEXMK := latexmk -pdf -interaction=nonstopmode -halt-on-error

DOCS := phase_1

.PHONY: all clean $(DOCS)

all: $(DOCS)

phase_1:
	cd phase_1 && $(LATEXMK) lowering.tex

clean:
	cd phase_1 && latexmk -C
