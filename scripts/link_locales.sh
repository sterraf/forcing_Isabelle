#!/bin/bash
session=$1 # link to this ---
src_dir=$2 # where are the lists of items of $session
href=$3    # where to link

function echolog {
    #
    # Echoes and writes to the logfile linking.log
    #
    echo $@ #| tee --append linking.log 
}

function link_item {
    #
    # Usage:
    # 
    #   link_item HTML ITEMLIST SUFFIX
    #echo Linking $1 >> linking_$1.log
    for z in `cat $2`
    do
	t=`echo $z | cut -d"." -f1`
	if [ $t".html" = $1 ]
	then
	    ctxt=`echo $z | cut -d"." -f2`
	    lprime=`echo $ctxt | sed -e "s/&/\\\\\\&/g"`
	    echo Item: $t.$l ---\> $t.$lprime ... >> linking_$1_locale.log
	    sed -i -e "s|\(<span class=\"command\">locale</span></span><span> </span><span\)>$ctxt<|\1 id=\"$t.$lprime\" class=\"pst-lnk\">$lprime</a><|g" $1
	    #echo  Done >> linking_$1.log
	fi
    done
}

function partial_job {
    #
    # Usage:
    #
    #   partial_job HTMLS ITEMLIST SUFFIX
    for y in $1
    do 
	link_item $y $2 $3
    done
}

function full_job {
    #
    # Usage:
    #
    #   full_job ITEMLIST SUFFIX LISTS
    for (( x=3; $#-$x ; x=$x+1))
    do 
	partial_job "${!x}" $1 $2
    done
    partial_job "${!#}" $1 $2
}

echo ${@:4} | grep "|"  -q && \
{ 
    echolog Error: a filename contains a pipe \("|"\).
    echolog Aborted
    exit 1
}
cat $src_dir/locale_assumptions_$session.txt | grep "|"  -q && \
{ 
    echolog Error: an item contains a pipe \("|"\).
    echolog Aborted
    exit 1
}

echolog -n Linking locales...
full_job $src_dir/locale_assumptions_$session.txt "" ${@:4}
echolog Finished
