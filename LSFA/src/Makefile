build: 
	isabelle build -c -D .
	tar -cvzf forcing.tar.gz Forcing_data.thy Forcing_notions.thy Gen_ext_pair.thy Names.thy Pointed_DC.thy ROOT document/


html: 
	isabelle env ISABELLE_BROWSER_INFO=./output/html  isabelle build -c -d . -o browser_info -v forcing
