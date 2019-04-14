#!/bin/bash
set -e

make

coqdoc -toc -interpolate -utf8 --latex -R . B_Unification -o all.tex intro.v \
	terms.v lowenheim_formula.v lowenheim_proof.v list_util.v poly.v \
	poly_unif.v sve.v -p "\\newtheorem{definition}{Definition}[section]"

pdflatex all

bibtex all

pdflatex all

pdflatex all

rm -f all.tex coqdoc.sty
