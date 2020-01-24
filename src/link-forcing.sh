#!/bin/bash
old_dir=$PWD
html_dir="output/html/ZF/Forcing/"
list1=Forces_Definition.html
list2="Forcing_Theorems.html Arities.html"
list3="Names.html Interface.html"
list4="Forcing_Main.html FrecR.html Nat_Miscellanea.html"
list5="Forcing_Notions.html Relative_Univ.html Forcing_Data.html\
 Renaming.html Internalizations.html"
list6="Replacement_Axiom.html Succession_Poset.html Recursion_Thms.html\
 Separation_Rename.html Choice_Axiom.html Least.html Pointed_DC.html\
 Renaming_Auto.html Union_Axiom.html"
list7="Ordinals_In_MG.html Powerset_Axiom.html Separation_Axiom.html\
 Foundation_Axiom.html Pairing_Axiom.html\
 Proper_Extension.html Rasiowa_Sikorski.html Extensionality_Axiom.html\
 Infinity_Axiom.html Synthetic_Definition.html"

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
    #   full_job ITEMLIST SUFFIX
    partial_job "$list1" $1 $2 &
    partial_job "$list2" $1 $2 &
    partial_job "$list3" $1 $2 &
    partial_job "$list4" $1 $2 &
    partial_job "$list5" $1 $2 &
    partial_job "$list6" $1 $2 &
    partial_job "$list7" $1 $2
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
full_job lemas.txt
echo  Done
echo -n Crosslinking "lemmas" items...
full_job lemaslemmas.txt
echo  Done
echo -n Crosslinking "definition" items...
full_job definiciones.txt _def
echo  Done
echo Changing to old directory
cd $old_dir
echo Finished
