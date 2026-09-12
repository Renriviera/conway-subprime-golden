.PHONY: pdf clean arxiv check

pdf:
	latexmk -pdf conway-subprime-proof.tex

clean:
	latexmk -C
	rm -f conway-subprime-proof.synctex.gz

arxiv:
	bash submission/package_arxiv.sh

check:
	python3 lean/scripts/check.py
