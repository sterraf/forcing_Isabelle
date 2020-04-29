OPTION = 

CHAPTER = ZF

SESSION = Forcing

OUT_DIR = output/html

ML_FILES = Renaming_ML.ml Utils.ml 

LINKING_DIR  = $(PWD)/../scripts
PARALLEL     = $(shell cat thy_files | egrep -v '^#' | sed s/\.thy/\.html/g )
THY_FILES    = $(shell cat thy_files | egrep -v '^#' | tr \" " ")
USR_HEAPS    = $(shell isabelle getenv ISABELLE_HEAPS | cut -f2 -d"=")
ML_ID        = $(shell isabelle getenv ML_IDENTIFIER | cut -f2 -d"=")
HEAP_LOG_DIR = $(USR_HEAPS)/$(ML_ID)/log
HTML_DIR     = $(OUT_DIR)/$(CHAPTER)/$(SESSION)
DB           = $(HEAP_LOG_DIR)/$(SESSION).db 

.PHONY: build html tar clean afp

$(DB):	thy_files $(THY_FILES) $(ML_FILES) Makefile document/root.tex \
		document/root.bib
	isabelle build $(OPTION) -v -c -d . $(SESSION)

build: 	$(DB)

$(HTML_DIR):	thy_files $(THY_FILES) $(ML_FILES) $(LINKING_DIR) ROOT \
			document/root.tex document/root.bib Makefile
	isabelle env \
	  ISABELLE_BROWSER_INFO=$(OUT_DIR)\
	  isabelle build $(OPTION) -d . -c -o browser_info -v $(SESSION)
	sh $(LINKING_DIR)/fix_links.sh  $(SESSION) $(CHAPTER) $(OUT_DIR)
	cat $(LINKING_DIR)/links.css >> $(HTML_DIR)/isabelle.css
	cd $(HTML_DIR); \
		bash $(LINKING_DIR)/parsing.sh $(SESSION); \
		bash $(LINKING_DIR)/linking.sh $(SESSION) . . $(PARALLEL)

html:	$(HTML_DIR)

$(SESSION).tar.gz:	$(HTML_DIR) Makefile_distro ROOT
	rm -rf tmptar
	mkdir tmptar
	mkdir tmptar/src
	cp README.md tmptar
	cp -r $(LINKING_DIR) tmptar/
	cp -r README.md $(PARALLELIZATION) thy_files $(THY_FILES) $(ML_FILES)\
	 ROOT document/ tmptar/src
	cp Makefile_distro tmptar/src/Makefile
	 ## Avoid temporary sed files from linking:
	rsync -ah --exclude 'sed*' $(HTML_DIR)/ tmptar/html
	tar --transform "s/tmptar/$(SESSION)/g" --show-transformed-names\
	 -cvzf $(SESSION).tar.gz tmptar
	rm -rf tmptar

tar:    $(SESSION).tar.gz

linked:	$(HTML_DIR) $(LINKING_DIR)/linking.sh Makefile_distro ROOT
	rm -rf tmptar
	mkdir tmptar
	mkdir tmptar/src
	cd $(HTML_DIR); \
		bash $(LINKING_DIR)/linking.sh ZF $(PWD)/../zf_item_lists/ \
		 https://cs.famaf.unc.edu.ar/~pedro/forcing/ZF $(PARALLEL); \
		bash $(LINKING_DIR)/linking.sh ZF-Constructible-Trans $(PWD)/../zf_item_lists/ \
		 https://cs.famaf.unc.edu.ar/~pedro/forcing/ZF-Constructible-Trans $(PARALLEL)
	cp README.md tmptar
	cp -r $(LINKING_DIR) tmptar/
	cp -r README.md $(PARALLELIZATION) thy_files $(THY_FILES) $(ML_FILES)\
	 ROOT document/ tmptar/src
	cp Makefile_distro tmptar/src/Makefile
	 ## Avoid temporary sed files from linking:
	rsync -ah --exclude 'sed*' $(HTML_DIR)/ tmptar/html
	tar --transform "s/tmptar/$(SESSION)/g" --show-transformed-names\
	 -cvzf $(SESSION).tar.gz tmptar
	rm -rf tmptar

$(SESSION)-AFP.tar.gz:    thy_files $(THY_FILES) $(ML_FILES) ROOT_AFP document/root.tex \
			  document/root.bib
	rm -rf tmpafp
	mkdir tmpafp
	cp $(THY_FILES) $(ML_FILES) tmpafp
	cp ROOT_AFP tmpafp/ROOT
	cp -r document/ tmpafp
	tar --transform "s/tmpafp/$(SESSION)/g" --show-transformed-names\
	 -cvzf $(SESSION)-AFP.tar.gz tmpafp

afp:	$(SESSION)-AFP.tar.gz

clean:
	rm -rf output/ tmptar tmpafp
