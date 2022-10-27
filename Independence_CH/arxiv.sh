#!/bin/bash

rootbase=independence_ch_isabelle
root=$rootbase.tex
bbl=$rootbase\_arxiv.bbl
arxiv_dir=__"$rootbase"_ArXiv_tmp
arxiv="$rootbase"_arxiv.tex
tgz="$rootbase"_arxiv.tar.gz
extra_files="llncs.cls"

if [ $rootbase.bbl -nt $bbl ]
then
   echo "Error: "$rootbase.bbl" newer than "$bbl"!"
   exit 1
fi

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

cp *sty $bbl $extra_files $arxiv_dir

cd $arxiv_dir

sed 's/\\bibliographystyle{[^}]*}//g' $root | \
    sed 's/\\bibliography{'$rootbase'}/\\input{'$bbl'}/g'\
 > $arxiv
rm -f $root

tar --exclude=$root -zcvf $tgz *tex *sty $bbl $extra_files
mv $tgz ..

cd ..

rm -rf $arxiv_dir

echo
echo "Beware:"
echo "        Don't forget to update \""$bbl"\" !"
