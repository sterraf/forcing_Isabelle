build: 
	isabelle build -c -D .

html: 
	isabelle env ISABELLE_BROWSER_INFO=./output/html  isabelle build -c -d . -o browser_info -v forcing

tar:    html
	sed -i -- 's/..\/..\/ZF\/ZF\/AC.html/https:\/\/www.cl.cam.ac.uk\/research\/hvg\/Isabelle\/dist\/library\/ZF\/ZF\/AC.html/g' ./output/html/Unsorted/forcing/Pointed_DC.html 
	sed -i -- 's/..\/..\/ZF\/ZF-Constructible\/Relative.html/https:\/\/www.cl.cam.ac.uk\/research\/hvg\/Isabelle\/dist\/library\/ZF\/ZF-Constructible\/Relative.html/g' ./output/html/Unsorted/forcing/Gen_ext_pair.html 
	tar --show-transformed-names -cvzf forcing.tar.gz Forcing_data.thy Forcing_notions.thy Gen_ext_pair.thy Names.thy Pointed_DC.thy ROOT Makefile README.md document/ output/html/Unsorted/forcing/ --transform s,output/html/Unsorted/forcing,html,
