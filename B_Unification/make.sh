#!/bin/bash
set -e

make

preamble="\\usepackage{graphicx} \\graphicspath{ {.} } \
\\newtheorem{definition}{Definition}[section]"

coqdoc -toc -interpolate -utf8 --latex -R . B_Unification -o all.tex introduction.v \
	terms.v lowenheim_formula.v lowenheim_proof.v list_util.v poly.v \
	poly_unif.v sve.v -p "$preamble"

awk 'NR==20{print "\\input{title.tex}"}1' all.tex > \
	all.tmp.tex && mv all.tmp.tex all.tex

pdflatex all

bibtex all

pdflatex all

pdflatex all

rm -f all.tex coqdoc.sty
