.PHONY: verify source-audit build kernel-audit paper clean

source-audit:
	python3 scripts/check_formalization.py

build:
	lake build

kernel-audit:
	lake env lean Verification.lean

verify: source-audit build kernel-audit

paper:
	cd paper && latexmk -pdf -interaction=nonstopmode -halt-on-error main.tex

clean:
	lake clean
	cd paper && latexmk -C main.tex || true
