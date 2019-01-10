TeX_FILES = abstract.tex intro_m.tex isabelle.tex zfc-axioms.tex\
   renaming.tex generic-extensions.tex recursion.tex hacking.tex\
   easy-axioms.tex forcing.tex proof-of-separation.tex\
   conclusion_m.tex appendix.tex 
EXTRA_FILES = isabelle.sty isabellesym.sty header-draft.tex\
   multidef.sty session_graph_colored.pdf
main = Separation_In_MG
tmp_dir = arXiv_tmp

build: 
	pdflatex -draftmode \\nonstopmode \\input $(main).tex
	bibtex $(main)
	pdflatex  -draftmode \\nonstopmode \\input $(main).tex
	pdflatex \\nonstopmode \\input $(main).tex

arXiv:	clean
	mkdir $(tmp_dir)
	cp $(EXTRA_FILES) separation_arxiv.bbl $(tmp_dir)
	bash kill_comments.sh $(TeX_FILES) separation_arxiv.tex
	bash fix_biblio.sh
	tar -cvf separation_arxiv.tar arXiv_tmp
	gzip separation_arxiv.tar

clean:
	rm -rf $(tmp_dir) separation_arxiv.tar.gz
