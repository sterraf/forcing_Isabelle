clean:
	rm -rf document/ output/ ROOT 

root: clean
	isabelle mkroot -d
	isabelle build -D .
	/bin/cp -f ROOTFILE ROOT

build: 
	isabelle build -D .
