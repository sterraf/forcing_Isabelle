#!/bin/bash

session=$1

## Script de indizado y linkeo de definiciones completo
echo -n Parsing "definition" items...
for x in *.html; do y=`basename -s".html" $x`; sed -i -e "h;s|.*<span class=\"entity\">\([^<>/ ]*\)</span>[ ]*<span class=\"main\">::.*|$y.GBL.\1|w definiciones__$y.txt" -e "g;s|<span\( class=\"entity\">\)\([^<>/ ]*\)\(</span>[ ]*<span class=\"main\">::\)|<span id=\"$y.GBL.\2\"\1\2\3|" $x ; done; cat definiciones__*txt > definiciones_$session.txt ; rm -f definiciones__*txt
echo  Done

## Script de indizado y linkeo de lemas
echo -n Parsing "lemma" items...
for x in *.html; do y=`basename -s".html" $x`; sed -i -e "h;s|.*lemma</span></span>[ ]\+\([^<>/ ]\+\)[ ]*<span.*|$y.GBL.\1|w lemas__$y.txt" -e "g;s|<span \(class=\"command\">lemma</span></span> \)\([^<>/ ]\+\)[ ]*<span|<span id=\"$y.GBL.\2\" \1\2 <span|" $x; done; cat lemas__*txt > lemas_$session.txt; rm -f lemas__*txt
echo  Done

## Script de indizado y linkeo de lemas en locales
echo -n Parsing "lemma (in locale)" items...
for x in *.html; do y=`basename -s".html" $x`; sed -i -e "h;s|.*lemma</span></span>[ ]\+\([^)]\+([^)]\+>in<[^)]\+\)\(<span class=\"main\">)</span>[ ]*\)\([^<>/ ]\+\)[ ]*<span.*|$y.GBL.\3|w lemas__$y.txt" -e "g;s|<span \(class=\"command\">lemma</span></span>[ ]*[^)]*([^)]\+>in<[^)]\+<span class=\"main\">)</span>[ ]*\)\([^<>/ ]\+\)[ ]*<span|<span id=\"$y.GBL.\2\" \1\2 <span|" $x; done; cat lemas__*txt >> lemas_$session.txt; rm -f lemas__*txt
echo  Done

## Script de indizado y linkeo de teoremas
echo -n Parsing "theorem" items...
for x in *.html; do y=`basename -s".html" $x`; sed -i -e "h;s|.*theorem</span></span>[ ]\+\([^<>/ ]\+\)[ ]*<span.*|$y.GBL.\1|w lemas__$y.txt" -e "g;s|<span \(class=\"command\">theorem</span></span> \)\([^<>/ ]\+\)[ ]*<span|<span id=\"$y.GBL.\2\" \1\2 <span|" $x; done; cat lemas__*txt >> lemas_$session.txt; rm -f lemas__*txt
echo  Done

## Script de indizado y linkeo de teoremas en locales
echo -n Parsing "theorem (in locale)" items...
for x in *.html; do y=`basename -s".html" $x`; sed -i -e "h;s|.*theorem</span></span>[ ]\+\([^)]\+([^)]\+>in<[^)]\+\)\(<span class=\"main\">)</span>[ ]*\)\([^<>/ ]\+\)[ ]*<span.*|$y.GBL.\3|w lemas__$y.txt" -e "g;s|<span \(class=\"command\">theorem</span></span>[ ]*[^)]*([^)]\+>in<[^)]\+<span class=\"main\">)</span>[ ]*\)\([^<>/ ]\+\)[ ]*<span|<span id=\"$y.GBL.\2\" \1\2 <span|" $x; done; cat lemas__*txt >> lemas_$session.txt; rm -f lemas__*txt
echo  Done

## Script de indizado y linkeo de goles esquematicos
echo -n Parsing "schematic_goal" items...
for x in *.html; do y=`basename -s".html" $x`; sed -i -e "h;s|.*schematic_goal</span></span>[ ]\+\([^<>/ ]\+\)[ ]*<span.*|$y.GBL.\1|w lemas__$y.txt" -e "g;s|<span \(class=\"command\">schematic_goal</span></span> \)\([^<>/ ]\+\)[ ]*<span|<span id=\"$y.GBL.\2\" \1\2 <span|" $x; done; cat lemas__*txt >> lemas_$session.txt; rm -f lemas__*txt
echo  Done

## Script de indizado y linkeo de "lemmas" (sic)
echo -n Parsing "lemmas" items...
for x in *.html; do y=`basename -s".html" $x`; sed -i -e "h;s|.*lemmas</span></span>[ ]\+\([^<>/ ]\+\).*|$y.GBL.\1|w lemas__$y.txt" -e "g;s|<span \(class=\"command\">lemmas</span></span>[ ]\+\)\([^<>/( ]\+\)[ ]*<span|<span id=\"$y.GBL.\2\" \1\2<span|" $x; done; cat lemas__*txt > lemaslemmas_$session.txt ; rm -f lemas__*txt
echo  Done

## Script de indizado y linkeo de locales
echo -n Parsing "locale" items...
for x in *.html; do y=`basename -s".html" $x`; sed -i -e "h;s|[^b]*>locale</span></span>[ ]\+\([^<>/ ]\+\).*|$y.\1.\1|w locales__$y.txt" -e "g;s|<span \(class=\"command\">locale</span></span>[ ]\+\)\([^<>/( ]\+\)[ ]*<span|<span id=\"$y.\2\" \1\2<span|" $x; done; cat locales__*txt > locales_$session.txt ; rm -f locales__*txt
echo  Done
