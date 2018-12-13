THY_FILES = Datatype_absolute  Forces_locale.thy Forcing_data.thy Forcing_notions.thy Infinity_Axiom.thy Interface.thy Internalizations.thy Names.thy Nat_Miscelanea.thy Pairing_Axiom.thy Pointed_DC.thy Recursion_Thms.thy Relative.thy Renaming.thy Separation_Axiom.thy Union_Axiom.thy Wellorderings.thy WF_absolute.thy WFrec.thy Foundation_Axiom.thy

build: 
	isabelle build -c -D .

html: 
	isabelle env ISABELLE_BROWSER_INFO=./output/html  isabelle build -c -d . -o browser_info -v Separation

tar:    html
	sh fix_links.sh
	tar --show-transformed-names -cvzf forcing.tar.gz $(THY_FILES) ROOT Makefile document/ output/html/Unsorted/Separation/ --transform s,output/html/Unsorted/Separation,html,
