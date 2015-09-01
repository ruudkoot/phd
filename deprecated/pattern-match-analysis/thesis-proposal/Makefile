all: thesis-proposal.pdf
	evince thesis-proposal.pdf

thesis-proposal.pdf: thesis-proposal.tex thesis-proposal.bib
	pdflatex thesis-proposal.tex
	bibtex thesis-proposal
	pdflatex thesis-proposal.tex
	pdflatex thesis-proposal.tex
