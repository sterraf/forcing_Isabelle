#!/bin/bash
session=$1 # link to this ---
src_dir=$2 # where are the lists of items of $session
href=$3    # where to link

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
	sed -i -e "s|>$l$3<|><a class=\"pst-lnk\" href=\"$href/$t.html#$t.$lprime\">$lprime$3</a><|g" $1
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

echo ${@:4} | grep "|"  -q && \
{ 
    echo Error: a filename contains a pipe \("|"\).
    echo Aborted
    exit 1
}
cat $src_dir/lemas_$session.txt $src_dir/lemaslemmas_$session.txt\
   $src_dir/definiciones_$session.txt | grep "|"  -q && \
{ 
    echo Error: an item contains a pipe \("|"\).
    echo Aborted
    exit 1
}

echo -n Crosslinking "lemma" items...
full_job $src_dir/lemas_$session.txt "" ${@:4}
echo  Done
echo -n Crosslinking "lemmas" items...
full_job $src_dir/lemaslemmas_$session.txt "" ${@:4}
echo  Done
echo -n Crosslinking "definition" items...
full_job $src_dir/definiciones_$session.txt _def ${@:4}
echo  Done
echo Finished
