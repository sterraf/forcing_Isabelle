TeX_FILES = abstract.tex intro_m.tex isabelle.tex zfc-axioms.tex\
   renaming.tex generic-extensions.tex recursion.tex hacking.tex\
   easy-axioms.tex forcing.tex proof-of-separation.tex\
   conclusion_m.tex appendix.tex 
EXTRA_FILES = isabelle.sty isabellesym.sty header-draft.tex\
   multidef.sty session_graph_colored.pdf
tmp_dir = arXiv_tmp

Separation_In_MG: main = Separation_In_MG
Separation_In_MG: build

separation_arxiv: main = separation_arxiv
separation_arxiv: build

build:
	pdflatex -draftmode \\nonstopmode \\input $(main).tex
	bibtex $(main)
	pdflatex  -draftmode \\nonstopmode \\input $(main).tex
	pdflatex \\nonstopmode \\input $(main).tex

arXiv:	clean separation_arxiv
	mkdir $(tmp_dir)
	cp $(EXTRA_FILES) separation_arxiv.bbl $(tmp_dir)
	bash kill_comments.sh $(TeX_FILES) separation_arxiv.tex
	bash fix_biblio.sh
	tar -cvf separation_arxiv.tar arXiv_tmp
	gzip separation_arxiv.tar

clean:
	rm -rf $(tmp_dir) separation_arxiv.tar.gz

diff:
	bash hacer_diff.sh
