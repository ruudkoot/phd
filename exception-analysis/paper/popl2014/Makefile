popl2014: popl2014.pdf
	evince popl2014.pdf

popl2014.pdf: popl2014.lhs2tex popl2014.bib
	lhs2tex -o popl2014.tex popl2014.lhs2tex
	pdflatex popl2014.tex
	bibtex popl2014
	pdflatex popl2014.tex
	pdflatex popl2014.tex
	
clean:
	rm *.aux *.bbl *.blg *.ptb
