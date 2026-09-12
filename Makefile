.PHONY: build check

build:
	cd lean && lake build

check:
	python3 lean/scripts/check.py
