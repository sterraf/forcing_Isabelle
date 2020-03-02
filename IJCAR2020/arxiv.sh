#!/bin/bash

sed 's/\\bibliographystyle{splncs04}//g' forcing_in_isabelle_zf.tex | \
 sed 's/\\bibliography{forcing_in_isabelle_zf}/\\input{forcing_in_isabelle_zf.bbl}/g'\
 > forcing_in_isabelle_zf_arxiv.tex

tar --exclude=forcing_in_isabelle_zf.tex -zcvf forcing_arxiv.tar.gz *tex *sty *cls *bbl 
rm -f forcing_in_isabelle_zf_arxiv.tex
