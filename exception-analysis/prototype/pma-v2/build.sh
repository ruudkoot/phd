#!/bin/bash
ghc -O3 --make Main && ./Main > output.tex && pdflatex output.tex && gv output.pdf
