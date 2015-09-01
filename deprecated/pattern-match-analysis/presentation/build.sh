#!/bin/bash
lhs2TeX presentation.tex > presentation.lhs2TeX.tex
pdflatex presentation.lhs2TeX.tex && pdflatex presentation.lhs2TeX.tex && mv presentation.lhs2TeX.pdf presentation.pdf && evince presentation.pdf
