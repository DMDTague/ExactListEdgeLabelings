.PHONY: verify source-audit build kernel-audit small-checks clean

source-audit:
	python3 scripts/check_formalization.py

build:
	lake build

kernel-audit:
	lake env lean Verification.lean

verify: source-audit build kernel-audit

small-checks:
	python3 checks/independent_small_checks.py

clean:
	lake clean
