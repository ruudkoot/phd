higher-ranked-exception-types.pdf: *.lhs2tex definitions/*.lhs2tex include/*.lhs2tex section/*.lhs2tex theorem/*.lhs2tex proof/*.lhs2tex figure/*.lhs2tex
	lhs2tex -o higher-ranked-exception-types.tex higher-ranked-exception-types.lhs2tex
	latexmk -pdf higher-ranked-exception-types.tex
	evince higher-ranked-exception-types.pdf

*.lhs2tex:
*.tex:
