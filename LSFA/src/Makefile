THY_FILES = Forcing_data.thy Forcing_notions.thy Gen_ext_pair.thy Names.thy Pointed_DC.thy

build: 
	isabelle build -c -D .

html: 
	isabelle env ISABELLE_BROWSER_INFO=./output/html  isabelle build -c -d . -o browser_info -v forcing

tar:    html
	sh fix_links.sh
	tar --show-transformed-names -cvzf forcing.tar.gz $(THY_FILES) ROOT Makefile README.md document/ output/html/Unsorted/forcing/ --transform s,output/html/Unsorted/forcing,html,
