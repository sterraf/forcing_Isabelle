#!/bin/bash
sed -i -- s@\bibliographystyle{mi-estilo-else}@@g arXiv_tmp/separation_arxiv.tex
sed -i -- s@\bibliography{../LSFA/citados}@\input{separation_arxiv.bbl}@g arXiv_tmp/separation_arxiv.tex

