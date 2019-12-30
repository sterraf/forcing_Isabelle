THY_FILES = Choice_Axiom.thy Datatype_absolute.thy\
 Extensionality_Axiom.thy Forces_Definition.thy Forcing_Data.thy\
 Forcing_Notions.thy Forcing_Theorems.thy Forcing_Thms.thy\
 Foundation_Axiom.thy FrecR.thy Infinity_Axiom.thy\
 Interface.thy Internalizations.thy Least.thy Names.thy\
 Nat_Miscellanea.thy Non_Constructible.thy Ordinals_In_MG.thy\
 Pairing_Axiom.thy Pointed_DC.thy Powerset_Axiom.thy Rank.thy\
 Rasiowa_Sikorski.thy Recursion_Thms.thy Relative.thy\
 Relative_Univ.thy Renaming.thy Renaming_Auto.thy Replacement_Axiom.thy\
 Separation_Axiom.thy Separation_Rename.thy Synthetic_Definition.thy\
 Union_Axiom.thy WF_absolute.thy WFrec.thy Wellorderings.thy 

build: 
	isabelle build -c -D .

html: 
	isabelle env ISABELLE_BROWSER_INFO=./output/html  isabelle build -c -d . -o browser_info -v Forcing

tar:    clean html
	sh fix_links.sh
	tar --show-transformed-names -cvzf forcing.tar.gz $(THY_FILES) ROOT Makefile document/ output/html/Unsorted/Forcing/ --transform s,output/html/Unsorted/Forcing,html,

clean:
	rm -rf output/
