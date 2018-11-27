THY_FILES = Pointed_DC.thy Forcing_notions.thy Forcing_data.thy Forces_locale.thy Names.thy Interface2.thy Renaming.thy Nat_Miscelanea.thy Pairing_Axiom.thy Union_Axiom.thy Separation_Axiom.thy

build: 
	isabelle build -c -D .

html: 
	isabelle env ISABELLE_BROWSER_INFO=./output/html  isabelle build -c -d . -o browser_info -v separation

tar:    html
	tar --show-transformed-names -cvzf forcing.tar.gz $(THY_FILES) ROOT Makefile document/ output/html/Unsorted/separation/ --transform s,output/html/Unsorted/separation,html,