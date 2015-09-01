#!/bin/bash
lhs2TeX thesis.tex > thesis.lhs2TeX.tex
pdflatex thesis.lhs2TeX.tex && bibtex thesis.lhs2TeX && makeindex thesis.lhs2TeX.idx && pdflatex thesis.lhs2TeX.tex && pdflatex thesis.lhs2TeX.tex && mv thesis.lhs2TeX.pdf thesis.pdf && evince thesis.pdf
