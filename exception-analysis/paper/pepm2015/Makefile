paper: paper.pdf
	evince paper.pdf

paper.pdf: paper.lhs2tex paper.bib
	lhs2tex -o paper.tex paper.lhs2tex
	pdflatex paper.tex
	bibtex paper
	pdflatex paper.tex
	pdflatex paper.tex
	
clean:
	rm *.aux *.bbl *.blg *.ptb
