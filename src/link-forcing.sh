#!/bin/bash
old_dir=$PWD
html_dir="output/html/Unsorted/Forcing/"

function link_item {
    #
    # Usage:
    # 
    #   link_item HTML ITEMLIST SUFFIX
    for z in `cat $2`
    do 
	l=`echo $z | cut -d"." -f2`$3
	lprime=`echo $l | sed -e "s/&/\\\\\\&/g"`
	t=`echo $z | cut -d"." -f1`
	sed -i -e "s/>$l</><a class=\"pst-lnk\" href=\"$t.html#$t.$lprime\">$lprime<\/a></g" $1
    done
}

function partial_job {
    #
    # Usage:
    #
    #   partial_job INITIALS ITEMLIST SUFFIX
    for x in [$1]*.html
    do 
	link_item $x $2 $3
    done
}

function full_job {
    #
    # Usage:
    #
    #   full_job ITEMLIST SUFFIX
    partial_job CDE $1 $2 &
    partial_job F $1 $2 &
    partial_job ILN $1 $2 &
    partial_job OPQ $1 $2 &
    partial_job RSTUVW $1 $2 
}

cd $html_dir

## Script de indizado y linkeo de definiciones completo
for x in *.html; do y=`basename -s".html" $x`; sed -i -e "h;s/.*definition<\/span><\/span><span>[ ]\+<\/span><span>\([^<>\/]*\)<\/span>.*/$y.\1/w definiciones_$y.sn.txt" -e "g;s/<span \(class=\"command\">definition<\/span><\/span><span> <\/span><span>\)\([^<>\/]*\)<\/span><span>/<span id=\"$y.\2\"\1\2<\/span><span>/" $x; sed -i -e "N;h;s/.*<span class=\"command\">definition<\/span><\/span><span>\n<\/span><span>[ ]\+<\/span><span>\([^<>\/]*\)<\/span><span>.*/$y.\1/w definiciones_$y.cn.txt" -e "g;s/<span \(class=\"command\">definition<\/span><\/span><span>\n<\/span><span>[ ]\+<\/span><span>\)\([^<>\/]*\)<\/span><span>/<span id=\"$y.\2\"\1\2<\/span><span>/;P;D" $x ; done; cat definiciones_*txt > definiciones.txt ; rm -f definiciones_*txt

## Script de indizado y linkeo de lemas
for x in *.html; do y=`basename -s".html" $x`; sed -i -e "h;s/.*lemma<\/span><\/span><span>[ ]\+<\/span><span>\([^<>\/]*\)<\/span>.*/$y.\1/w lemas_$y.sn.txt" -e "g;s/<span \(class=\"command\">lemma<\/span><\/span><span> <\/span><span>\)\([^<>\/]*\)<\/span>/<span id=\"$y.\2\" \1\2<\/span>/" $x; done; cat lemas_*txt > lemas.txt ; rm -f lemas_*txt
 
## Script de indizado y linkeo de "lemmas" (sic)
for x in *.html; do y=`basename -s".html" $x`; sed -i -e "h;s/.*lemmas<\/span><\/span><span>[ ]\+<\/span><span>\([^<>\/]*\)<\/span>.*/$y.\1/w lemas_$y.sn.txt" -e "g;s/<span \(class=\"command\">lemmas<\/span><\/span><span> <\/span><span>\)\([^<>\/]*\)<\/span>/<span id=\"$y.\2\" \1\2<\/span>/" $x; done; cat lemas_*txt > lemaslemmas.txt ; rm -f lemas_*txt

full_job lemas.txt
full_job lemaslemmas.txt
full_job definiciones.txt _def

cd $old_dir
