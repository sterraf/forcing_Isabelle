#!/bin/bash

session=$1

## Script de indizado y linkeo de definiciones completo
echo -n Parsing "definition" items...
for x in *.html; do y=`basename -s".html" $x`; sed -i -e "h;s/.*definition<\/span><\/span><span>[ ]\+<\/span><span>\([^<>\/]*\)<\/span>.*/$y.\1/w definiciones__$y.sn.txt" -e "g;s/<span \(class=\"command\">definition<\/span><\/span><span> <\/span><span>\)\([^<>\/]*\)<\/span><span>/<span id=\"$y.\2\"\1\2<\/span><span>/" $x; sed -i -e "N;h;s/.*<span class=\"command\">definition<\/span><\/span><span>\n<\/span><span>[ ]\+<\/span><span>\([^<>\/]*\)<\/span><span>.*/$y.\1/w definiciones__$y.cn.txt" -e "g;s/<span \(class=\"command\">definition<\/span><\/span><span>\n<\/span><span>[ ]\+<\/span><span>\)\([^<>\/]*\)<\/span><span>/<span id=\"$y.\2\"\1\2<\/span><span>/;P;D" $x ; done; cat definiciones__*txt > definiciones_$session.txt ; rm -f definiciones__*txt

## Script de indizado y linkeo de lemas
echo  Done
echo -n Parsing "lemma" items...
for x in *.html; do y=`basename -s".html" $x`; sed -i -e "h;s/.*lemma<\/span><\/span><span>[ ]\+<\/span><span>\([^<>\/]*\)<\/span>.*/$y.\1/w lemas__$y.sn.txt" -e "g;s/<span \(class=\"command\">lemma<\/span><\/span><span> <\/span><span>\)\([^<>\/]*\)<\/span>/<span id=\"$y.\2\" \1\2<\/span>/" $x; done; cat lemas__*txt > lemas_$session.txt ; rm -f lemas__*txt
 
## Script de indizado y linkeo de "lemmas" (sic)
echo  Done
echo -n Parsing "lemmas" items...
for x in *.html; do y=`basename -s".html" $x`; sed -i -e "h;s/.*lemmas<\/span><\/span><span>[ ]\+<\/span><span>\([^<>\/]*\)<\/span>.*/$y.\1/w lemas__$y.sn.txt" -e "g;s/<span \(class=\"command\">lemmas<\/span><\/span><span> <\/span><span>\)\([^<>\/]*\)<\/span>/<span id=\"$y.\2\" \1\2<\/span>/" $x; done; cat lemas__*txt > lemaslemmas_$session.txt ; rm -f lemas__*txt
echo  Done
