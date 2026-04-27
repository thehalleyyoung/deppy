# Build the PSDL treatise.
#
# Targets:
#   make            -- run pdflatex three times (so cleveref / TOC settle)
#                      followed by biber if refs.bib has citations.
#   make once       -- single pdflatex pass (fast, missing refs).
#   make clean      -- remove .aux .log .toc .out .lof .lot .bbl .bcf .blg
#   make distclean  -- clean + remove main.pdf
#
# This Makefile assumes a TeX Live or MacTeX install with pdflatex,
# biber, and the listed LaTeX packages:
#   amsmath, amssymb, amsthm, mathtools, mathpartir, stmaryrd
#   tikz, tikz-cd
#   listings
#   biblatex (backend=biber)
#   hyperref, cleveref
#   booktabs, longtable, tabularx
#   geometry, microtype, lmodern, parskip, enumitem
#
# On TeX Live: `tlmgr install mathpartir tikz-cd biblatex biber stmaryrd`
# is usually enough on a base install.

LATEX     := pdflatex -interaction=nonstopmode -halt-on-error
BIBER     := biber
MAIN      := main

CHAPTERS := \
  ch01_intro.tex   ch02_dependent.tex  ch03_python.tex   \
  ch04_cubical.tex ch05_deppy.tex      ch06_psdl.tex     \
  ch07_pipeline.tex ch08_lean.tex      ch09_z3.tex       \
  ch10_cohomology.tex ch11_examples.tex ch12_soundness.tex \
  ch13_related.tex

.PHONY: all once clean distclean

all: $(MAIN).pdf

$(MAIN).pdf: $(MAIN).tex $(CHAPTERS) refs.bib
	$(LATEX) $(MAIN)
	-$(BIBER) $(MAIN) || true
	$(LATEX) $(MAIN)
	$(LATEX) $(MAIN)

once:
	$(LATEX) $(MAIN)

clean:
	rm -f *.aux *.log *.toc *.lof *.lot *.bbl *.bcf *.blg *.out *.idx *.ilg *.ind *.run.xml *.synctex.gz

distclean: clean
	rm -f $(MAIN).pdf
