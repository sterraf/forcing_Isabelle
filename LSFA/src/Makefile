clean:
	rm -rf document/ output/ ROOT 

root: clean
	isabelle mkroot -d
	/bin/cp -f ROOTFILE ROOT

build: ROOT
	isabelle build -D .
