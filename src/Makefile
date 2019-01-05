THY_FILES = Datatype_absolute.thy Extensionality_Axiom.thy
 Forcing_Theorems.thy Forcing_Data.thy Forcing_Notions.thy\
 Foundation_Axiom.thy Infinity_Axiom.thy Interface.thy\
 Internalizations.thy Names.thy Nat_Miscelanea.thy Pairing_Axiom.thy\
 Pointed_DC.thy Powerset_Axiom.thy Recursion_Thms.thy Relative.thy\
 Renaming.thy Separation_Axiom.thy Union_Axiom.thy Wellorderings.thy\
 WF_absolute.thy WFrec.thy 

build: 
	isabelle build -c -D .

html: 
	isabelle env ISABELLE_BROWSER_INFO=./output/html  isabelle build -c -d . -o browser_info -v Separation

tar:    clean html
	sh fix_links.sh
	tar --show-transformed-names -cvzf forcing.tar.gz $(THY_FILES) ROOT Makefile document/ output/html/Unsorted/Separation/ --transform s,output/html/Unsorted/Separation,html,

clean:
	rm -rf output/
