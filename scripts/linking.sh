#!/bin/bash
session=$1 # link to this ---
src_dir=$2 # where are the lists of items of $session
href=$3    # where to link

function echolog {
    #
    # Echoes and writes to the logfile linking.log
    #
    echo $@ # | tee --append linking.log
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
	ctxt=`echo $z | cut -d"." -f2`
	l=`echo $z | cut -d"." -f3`
	lprime=`echo $l | sed -e "s/&/\\\\\\&/g"`
	if [ $ctxt = "GBL" ];
	then
	    link=.$lprime
	else
	    link=""
	fi
	# echo Item: $t.$l ---\> $t.$lprime ... >> linking_$1.log
	sed -i -e "s%\(^\|[^_\.[:alnum:]]\)$l$3\([^_\.[:alnum:]]\|$\)%\1<a class=\"pst-lnk\" href=\"$href/$t.html#$t.$ctxt$link\">$lprime$3</a>\2%g" $1
	# echo  Done >> linking_$1.log
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
	partial_job "${!x}" $1 $2 &
    done
    partial_job "${!#}" $1 $2
}

# echo ${@:4} | grep "|"  -q && \
# { 
#     echolog Error: a filename contains a pipe \("|"\).
#     echolog Aborted
#     exit 1
# }
# cat $src_dir/lemas_$session.txt $src_dir/lemaslemmas_$session.txt\
#    $src_dir/definiciones_$session.txt | grep "|"  -q && \
# { 
#     echolog Error: an item contains a pipe \("|"\).
#     echolog Aborted
#     exit 1
# }

echolog -n Crosslinking "lemma" items...
full_job $src_dir/lemas_$session.txt "" ${@:4}
echolog  Done
echolog -n Crosslinking locales...
full_job $src_dir/locales_$session.txt "" ${@:4}
echolog  Done
echolog -n Crosslinking locale assumptions...
full_job $src_dir/locale_assumptions_$session.txt "" ${@:4}
echolog  Done
echolog -n Crosslinking "lemmas" items...
full_job $src_dir/lemaslemmas_$session.txt "" ${@:4}
echolog  Done
echolog -n Crosslinking "definition" items...
full_job $src_dir/definiciones_$session.txt _def ${@:4}
echolog  Done
echolog Finished
