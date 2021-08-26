#!/bin/bash

session=$1

function parse_basic {
    #
    # Parse item
    #
    echo -n Parsing \"$1\" items...
    for x in *.html; do y=`basename -s".html" $x`; sed -i -e "h;s|.*$1</span></span>[ ]\+\([^<>/ ]\+\)[ ]*<span.*|$y.GBL.\1|w lemas__$y.txt" -e "g;s|<span \(class=\"command\">$1</span></span> \)\([^<>/ ]\+\)[ ]*<span|<span id=\"$y.GBL.\2\" \1\2 <span|" $x; done; cat lemas__*txt >> lemas_$session.txt; rm -f lemas__*txt
    echo  Done
}

function parse_in_locale {
    echo -n Parsing \"$1 "(in locale)"\" items...
    for x in *.html; do y=`basename -s".html" $x`; sed -i -e "h;s|.*$1</span></span>[ ]\+\([^)]\+([^)]\+>in<[^)]\+\)\(<span class=\"main\">)</span>[ ]*\)\([^<>/ ]\+\)[ ]*<span.*|$y.GBL.\3|w lemas__$y.txt" -e "g;s|<span \(class=\"command\">$1</span></span>[ ]*[^)]*([^)]\+>in<[^)]\+<span class=\"main\">)</span>[ ]*\)\([^<>/ ]\+\)[ ]*<span|<span id=\"$y.GBL.\2\" \1\2 <span|" $x; done; cat lemas__*txt >> lemas_$session.txt; rm -f lemas__*txt
    echo  Done
}

## Script de indizado y linkeo de definiciones completo
echo -n Parsing "definition" items...
for x in *.html; do y=`basename -s".html" $x`; sed -i -e "h;s|.*<span class=\"entity\">\([^<>/ ]*\)</span>[ ]*<span class=\"main\">::.*|$y.GBL.\1|w definiciones__$y.txt" -e "g;s|<span\( class=\"entity\">\)\([^<>/ ]*\)\(</span>[ ]*<span class=\"main\">::\)|<span id=\"$y.GBL.\2\"\1\2\3|" $x ; done; cat definiciones__*txt > definiciones_$session.txt ; rm -f definiciones__*txt
echo  Done

## Script de indizado y linkeo de lemas
parse_basic "lemma"

## Script de indizado y linkeo de lemas en locales
parse_in_locale "lemma"

## Script de indizado y linkeo de teoremas
parse_basic "theorem"

## Script de indizado y linkeo de teoremas en locales
parse_in_locale "theorem"

## Script de indizado y linkeo de goles esquematicos
parse_basic "schematic_goal"

## Script de indizado y linkeo de "lemmas" (sic)
echo -n Parsing "lemmas" items...
for x in *.html; do y=`basename -s".html" $x`; sed -i -e "h;s|.*lemmas</span></span>[ ]\+\([^<>/ ]\+\).*|$y.GBL.\1|w lemas__$y.txt" -e "g;s|<span \(class=\"command\">lemmas</span></span>[ ]\+\)\([^<>/( ]\+\)[ ]*<span|<span id=\"$y.GBL.\2\" \1\2<span|" $x; done; cat lemas__*txt > lemaslemmas_$session.txt ; rm -f lemas__*txt
echo  Done

## Script de indizado y linkeo de locales
echo -n Parsing "locale" items...
for x in *.html; do y=`basename -s".html" $x`; sed -i -e "h;s|[^b]*>locale</span></span>[ ]\+\([^<>/ ]\+\).*|$y.\1.\1|w locales__$y.txt" -e "g;s|<span \(class=\"command\">locale</span></span>[ ]\+\)\([^<>/( ]\+\)[ ]*<span|<span id=\"$y.\2\" \1\2<span|" $x; done; cat locales__*txt > locales_$session.txt ; rm -f locales__*txt
echo  Done
