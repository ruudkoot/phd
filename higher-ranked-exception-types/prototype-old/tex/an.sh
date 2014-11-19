#!/bin/bash
ghc -O --make Main
./Main > an.lhs2tex
lhs2tex -o an.tex an.lhs2tex
latexmk -pdf an.tex
evince an.pdf
