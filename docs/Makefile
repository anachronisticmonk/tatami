# Build the design documents. `make` builds everything, `make phase_1` one of them.
#
# Each document is a directory holding one or more top-level .tex files. Add a
# directory to DOCS and a rule below and it builds with the rest.

LATEXMK := latexmk -pdf -interaction=nonstopmode -halt-on-error

DOCS := phase_1

.PHONY: all clean pipeline $(DOCS)

all: $(DOCS) pipeline

phase_1:
	cd phase_1 && $(LATEXMK) lowering.tex

# One document is HTML rather than LaTeX: it is diagram-led, and the diagrams
# are inline SVG. Chrome prints it; the print rules live in the page.
pipeline:
	cd phase_1 && google-chrome --headless=new --disable-gpu --no-pdf-header-footer \
	  --virtual-time-budget=20000 --print-to-pdf=pipeline.pdf pipeline.html

clean:
	cd phase_1 && latexmk -C
