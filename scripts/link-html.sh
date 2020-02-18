#!/bin/bash
old_dir=$PWD
html_dir="output/html/ZF/$1/"

function link_item {
    #
    # Usage:
    # 
    #   link_item HTML ITEMLIST SUFFIX
    for z in `cat $2`
    do 
	l=`echo $z | cut -d"." -f2`
	lprime=`echo $l | sed -e "s/&/\\\\\\&/g"`
	t=`echo $z | cut -d"." -f1`
	sed -i -e "s/>$l$3</><a class=\"pst-lnk\" href=\"$t.html#$t.$lprime\">$lprime$3<\/a></g" $1
    done
}

function partial_job {
    #
    # Usage:
    #
    #   partial_job HTMLS ITEMLIST SUFFIX
    for x in $1
    do 
	link_item $x $2 $3
    done
}

function full_job {
    #
    # Usage:
    #
    #   full_job ITEMLIST SUFFIX LISTS
    for (( x=3; $#-$x ; x=$x+1))
    do 
	partial_job "${!x}" $1 $2 &
    done
    partial_job "${!#}" $1 $2
}

# echo Back-up of html directory
# cp -R $html_dir ~/tmp/

echo Changing to html directory
cd $html_dir

## Script de indizado y linkeo de definiciones completo
echo -n Parsing "definition" items...
for x in *.html; do y=`basename -s".html" $x`; sed -i -e "h;s/.*definition<\/span><\/span><span>[ ]\+<\/span><span>\([^<>\/]*\)<\/span>.*/$y.\1/w definiciones_$y.sn.txt" -e "g;s/<span \(class=\"command\">definition<\/span><\/span><span> <\/span><span>\)\([^<>\/]*\)<\/span><span>/<span id=\"$y.\2\"\1\2<\/span><span>/" $x; sed -i -e "N;h;s/.*<span class=\"command\">definition<\/span><\/span><span>\n<\/span><span>[ ]\+<\/span><span>\([^<>\/]*\)<\/span><span>.*/$y.\1/w definiciones_$y.cn.txt" -e "g;s/<span \(class=\"command\">definition<\/span><\/span><span>\n<\/span><span>[ ]\+<\/span><span>\)\([^<>\/]*\)<\/span><span>/<span id=\"$y.\2\"\1\2<\/span><span>/;P;D" $x ; done; cat definiciones_*txt > definiciones.txt ; rm -f definiciones_*txt

## Script de indizado y linkeo de lemas
echo  Done
echo -n Parsing "lemma" items...
for x in *.html; do y=`basename -s".html" $x`; sed -i -e "h;s/.*lemma<\/span><\/span><span>[ ]\+<\/span><span>\([^<>\/]*\)<\/span>.*/$y.\1/w lemas_$y.sn.txt" -e "g;s/<span \(class=\"command\">lemma<\/span><\/span><span> <\/span><span>\)\([^<>\/]*\)<\/span>/<span id=\"$y.\2\" \1\2<\/span>/" $x; done; cat lemas_*txt > lemas.txt ; rm -f lemas_*txt
 
## Script de indizado y linkeo de "lemmas" (sic)
echo  Done
echo -n Parsing "lemmas" items...
for x in *.html; do y=`basename -s".html" $x`; sed -i -e "h;s/.*lemmas<\/span><\/span><span>[ ]\+<\/span><span>\([^<>\/]*\)<\/span>.*/$y.\1/w lemas_$y.sn.txt" -e "g;s/<span \(class=\"command\">lemmas<\/span><\/span><span> <\/span><span>\)\([^<>\/]*\)<\/span>/<span id=\"$y.\2\" \1\2<\/span>/" $x; done; cat lemas_*txt > lemaslemmas.txt ; rm -f lemas_*txt
echo  Done

echo -n Crosslinking "lemma" items...
full_job lemas.txt "" ${@:2}
echo  Done
echo -n Crosslinking "lemmas" items...
full_job lemaslemmas.txt "" ${@:2}
echo  Done
echo -n Crosslinking "definition" items...
full_job definiciones.txt _def ${@:2}
echo  Done
echo Changing to old directory
# echo -n Waiting for 'sed' to clean temp files...
# while [ -f sed[^\.]* ]; do sleep 1; done
# echo  Done
cd $old_dir
echo Finished
