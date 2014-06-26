paper: paper.pdf
	evince paper.pdf

paper.pdf: paper.lhs2tex section/* ../higher-ranked-exception-types.bib
	lhs2tex -o paper.tex paper.lhs2tex
	latexmk -pdf paper.tex

clean:
	rm *.aux *.bbl *.blg *.ptb
