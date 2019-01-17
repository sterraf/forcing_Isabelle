#!/bin/bash
DIFF_DIR=diff_dir
PREFIX=LICS
OLD_DIR=$DIFF_DIR/$PREFIX"_old"
NEW_DIR=$DIFF_DIR/$PREFIX"_new"
## SHA for testing purposes
OLDSHA=73ed3222f1edb01dd260f7ea7f9bfe4acb785fa5
## SHA of submitted version (the real thing)
# OLDSHA=457792cabb9db838fe26a23a9b70d735423a45c0
MAIN=Separation_In_MG

function clear_appendix {
    sed -i -- 's@\\appendix\[A short overview of our development\]@@g' $1
    sed -i -- 's@\\input{appendix}@@g' $1
    sed -i -- 's@\\newpage\n\\onecolumn@@g' $1
}

mkdir $DIFF_DIR
rm -rf $DIFF_DIR/*
mkdir $OLD_DIR $NEW_DIR
git archive $OLDSHA | tar -x -C $OLD_DIR
cp * $NEW_DIR
clear_appendix $OLD_DIR/$MAIN.tex
clear_appendix $NEW_DIR/$MAIN.tex
cd $DIFF_DIR
latexdiff --flatten $PREFIX"_old"/$MAIN.tex $PREFIX"_new"/$MAIN.tex > $PREFIX"_new"/diff.tex
cd $PREFIX"_new"/
sed -i -- 's/Local Variables://g' diff.tex
sed -i -- 's@bibliography{../LSFA/citados}@bibliography{../../../LSFA/citados}@g' diff.tex
pdflatex \\nonstopmode\\input diff.tex
pdflatex \\nonstopmode\\input diff.tex
bibtex diff.aux
pdflatex \\nonstopmode\\input diff.tex
pdflatex \\nonstopmode\\input diff.tex
