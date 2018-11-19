#!/bin/bash

mkdir diff_dir
rm -rf diff_dir/*
mkdir diff_dir/LSFA_old/ diff_dir/LSFA_new/
git archive 80e6d1835fc9da4394d0c805d70c3032f6ba297d | tar -x -C diff_dir/LSFA_old
# cp * diff_dir/LSFA_old/
# git checkout new_design
cp * diff_dir/LSFA_new/
cd diff_dir
latexdiff --flatten LSFA_old/first_steps_into_forcing.tex LSFA_new/first_steps_into_forcing.tex > LSFA_new/diff.tex
cd LSFA_new/
sed -i -- 's/Local Variables://g' diff.tex
sed -i -- 's/bibliographystyle{entcs}/bibliographystyle{mi-estilo-else}/g' diff.tex
cp ../../arXiv/mi-estilo-else.bst .
cp diff.tex diff.tmp
cat ../../header-of-diff.tex > diff.tex
tail -n +67 diff.tmp >> diff.tex
pdflatex diff.tex
pdflatex diff.tex
bibtex diff.aux
pdflatex diff.tex
pdflatex diff.tex
