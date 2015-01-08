higher-ranked-exception-types.pdf: *.lhs2tex
	lhs2tex -o presentation.tex presentation.lhs2tex
	latexmk -pdf presentation.tex
	evince presentation.pdf

*.lhs2tex:
*.tex:
