#!/bin/bash

rootbase=independence_ch_isabelle
root=$rootbase.tex
arxiv_dir=__"$rootbase"_ArXiv_tmp
arxiv="$rootbase"_arxiv.tex
tgz="$rootbase"_arxiv.tar.gz
extra_files="llncs.cls"

pdflatex -draftmode \\nonstopmode \\input $root > /dev/null
bibtex $rootbase
makeindex $rootbase
pdflatex  -draftmode \\nonstopmode \\input $root > /dev/null
pdflatex \\nonstopmode \\input $root

mkdir $arxiv_dir

for x in *.tex
do
    ../scripts/stripcomments.pl $x > $arxiv_dir/$x
done

cp *sty *bbl $extra_files $arxiv_dir

cd $arxiv_dir

sed 's/\\bibliographystyle{[^}]*}//g' $root | \
    sed 's/\\bibliography{'$rootbase'}/\\input{'$rootbase.bbl'}/g'\
 > $arxiv
rm -f $root

tar --exclude=$root -zcvf $tgz *tex *sty *cls *bbl $extra_files
mv $tgz ..

cd ..

rm -rf $arxiv_dir
