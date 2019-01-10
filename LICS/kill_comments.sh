#!/bin/bash
for x in $*; do ./stripcomments.pl $x > arXiv_tmp/$x; done
