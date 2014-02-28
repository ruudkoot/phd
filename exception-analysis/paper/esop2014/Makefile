tbea: tbea.pdf
	evince tbea.pdf

tbea.pdf: tbea.lhs2tex tbea.bib
	lhs2tex -o tbea.tex tbea.lhs2tex
	pdflatex tbea.tex
	bibtex tbea
	pdflatex tbea.tex
	pdflatex tbea.tex
	
clean:
	rm *.aux *.bbl *.blg *.ptb
