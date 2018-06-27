build: 
	isabelle build -c -D .

html: 
	isabelle env ISABELLE_BROWSER_INFO=./output/html  isabelle build -c -d . -o browser_info -v forcing

tar:    html
	tar --show-transformed-names -cvzf forcing.tar.gz Forcing_data.thy Forcing_notions.thy Gen_ext_pair.thy Names.thy Pointed_DC.thy ROOT document/ output/html/Unsorted/forcing/ --transform s,output/html/Unsorted/forcing,html,
