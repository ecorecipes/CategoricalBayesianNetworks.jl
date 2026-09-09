.PHONY: build cache audit check-certificates dependencies docs mdgen html pdf diagrams clean

LIB := CategoricalBayesianNetworksProofs
TITLE := Finite Typed Open Networks: Semantics and Checked JSON
AUTHOR := Simon Frost
MD_FILES := Syntax.md Category.md Tensor.md Wiring.md Monoidal.md CopyDiscard.md Legged.md \
	Pushout.md Examples.md Assignments.md Semantics.md Normalization.md SemanticTensor.md \
	InterpretationFunctor.md ApexEnumeration.md RawCertificate.md LocalTables.md \
	SemanticExamples.md CertificateExamples.md CertificateSyntax.md CertificateJSON.md
JULIAMONO_DIR := $(abspath ../../fonts/JuliaMono)/
PANDOC_COMMON := --toc --toc-depth=2 --syntax-definition=lean.xml --syntax-highlighting=tango \
	--metadata title="$(TITLE)" --metadata author="$(AUTHOR)" --metadata date="2026-09-08"

build:
	lake build --wfail

cache:
	lake exe cache get

audit:
	lake env lean Audit.lean > audit.log
	cat audit.log
	python3 scripts/audit.py audit.log
	python3 scripts/test_audit.py

check-certificates:
	lake build check_certificate --wfail
	lake exe check_certificate certificate-fixtures/mixed.json
	python3 scripts/test_certificates.py

dependencies:
	python3 scripts/dependency_inventory.py

docs: mdgen html pdf

diagrams:
	dot -Tsvg diagrams/mixed.dot -o diagrams/mixed.svg
	dot -Tpdf diagrams/mixed.dot -o diagrams/mixed.pdf
	dot -Tsvg diagrams/stochastic.dot -o diagrams/stochastic.svg
	dot -Tpdf diagrams/stochastic.dot -o diagrams/stochastic.pdf

mdgen: diagrams
	lake exe mdgen $(LIB) .mdgen
	@for f in $(MD_FILES); do \
	  printf '\n\n<!-- $(LIB)/%s -->\n\n' "$${f%.md}.lean"; \
	  perl -0pe 's/\A(```lean\n(?:import [^\n]*\n)+```\n\n)(\# [^\n]*\n\n)/$$2$$1/' .mdgen/$$f; \
	done > $(LIB).md
	@printf '\n\n# Certificate checker executable\n\n```lean\n' >> $(LIB).md
	@cat CertificateMain.lean >> $(LIB).md
	@printf '\n```\n' >> $(LIB).md
	rm -rf .mdgen

html: $(LIB).md
	pandoc $(LIB).md -o $(LIB).html --standalone --mathjax --css=style.css $(PANDOC_COMMON)

pdf: $(LIB).md
	printf '\\newcommand{\\JuliaMonoDir}{%s}\n' "$(JULIAMONO_DIR)" > .fonts.tex
	pandoc $(LIB).md -o $(LIB).tex --standalone $(PANDOC_COMMON) \
		--lua-filter=scripts/pdf-images.lua -V papersize=a4 -V geometry:margin=2.2cm \
		-V colorlinks=true -V linkcolor=NavyBlue -V urlcolor=NavyBlue -V toccolor=black \
		-H .fonts.tex -H header.tex
	lualatex -interaction=nonstopmode -halt-on-error $(LIB).tex > latex-first.log
	lualatex -interaction=nonstopmode -halt-on-error $(LIB).tex > latex-second.log
	lualatex -interaction=nonstopmode -halt-on-error $(LIB).tex > latex-third.log
	@if grep -q "Missing character" $(LIB).log; then \
	  grep "Missing character" $(LIB).log; exit 1; fi
	@echo "PDF built with no missing-character warnings."

clean:
	rm -rf .mdgen .fonts.tex .inspection
	rm -f $(LIB).aux $(LIB).log $(LIB).out $(LIB).toc $(LIB).tex \
		latex-first.log latex-second.log latex-third.log
