OPTION = 

CHAPTER = ZF

SESSION = Forcing

OUT_DIR = output/html

ML_FILES = Renaming_ML.ml

LINKING_DIR  = $(PWD)/../scripts
PARALLEL     = $(shell cat thy_files | sed s/\.thy/\.html/g )
THY_FILES    = $(shell cat thy_files | tr \" " ")
USR_HEAPS    = $(shell isabelle getenv ISABELLE_HEAPS | cut -f2 -d"=")
ML_ID        = $(shell isabelle getenv ML_IDENTIFIER | cut -f2 -d"=")
HEAP_LOG_DIR = $(USR_HEAPS)/$(ML_ID)/log
HTML_DIR     = $(OUT_DIR)/$(CHAPTER)/$(SESSION)
DB           = $(HEAP_LOG_DIR)/$(SESSION).db 

.PHONY: build html tar clean

$(DB):	thy_files $(THY_FILES) $(ML_FILES)
	isabelle build $(OPTION) -v -c -d . $(SESSION)

build: 	$(DB)

$(HTML_DIR):	thy_files $(THY_FILES) $(ML_FILES) $(LINKING_DIR) ROOT
	isabelle env \
	  ISABELLE_BROWSER_INFO=$(OUT_DIR)\
	  isabelle build $(OPTION) -d . -c -o browser_info -v $(SESSION)
	sh $(LINKING_DIR)/fix_links.sh  $(SESSION) $(CHAPTER) $(OUT_DIR)
	cat $(LINKING_DIR)/links.css >> $(HTML_DIR)/isabelle.css
	cd $(HTML_DIR); \
		bash $(LINKING_DIR)/parsing.sh $(SESSION); \
		bash $(LINKING_DIR)/linking.sh $(SESSION) . . $(PARALLEL)

html:	$(HTML_DIR)

$(SESSION).tar.gz:	$(HTML_DIR) Makefile Makefile_distro ROOT
	rm -rf tmptar
	mkdir tmptar
	mkdir tmptar/src
	cp README tmptar
	cp -r $(LINKING_DIR) tmptar/
	cp -r README $(PARALLELIZATION) thy_files $(THY_FILES) $(ML_FILES)\
	 ROOT document/ tmptar/src
	cp Makefile_distro tmptar/src/Makefile
	 ## Avoid temporary sed files from linking:
	rsync -ah --exclude 'sed*' $(HTML_DIR)/ tmptar/html
	tar --transform "s/tmptar/$(SESSION)/g" --show-transformed-names\
	 -cvzf $(SESSION).tar.gz tmptar
	rm -rf tmptar

tar:    $(SESSION).tar.gz

linked:	$(HTML_DIR) $(LINKING_DIR)/linking.sh Makefile Makefile_distro ROOT
	rm -rf tmptar
	mkdir tmptar
	mkdir tmptar/src
	cd $(HTML_DIR); \
		bash $(LINKING_DIR)/linking.sh ZF $(PWD)/../zf_item_lists/ \
		 https://cs.famaf.unc.edu.ar/~pedro/forcing/ZF $(PARALLEL); \
		bash $(LINKING_DIR)/linking.sh ZF-Constructible-Trans $(PWD)/../zf_item_lists/ \
		 https://cs.famaf.unc.edu.ar/~pedro/forcing/ZF-Constructible-Trans $(PARALLEL)
	cp README tmptar
	cp -r $(LINKING_DIR) tmptar/
	cp -r README $(PARALLELIZATION) thy_files $(THY_FILES) $(ML_FILES)\
	 ROOT document/ tmptar/src
	cp Makefile_distro tmptar/src/Makefile
	 ## Avoid temporary sed files from linking:
	rsync -ah --exclude 'sed*' $(HTML_DIR)/ tmptar/html
	tar --transform "s/tmptar/$(SESSION)/g" --show-transformed-names\
	 -cvzf $(SESSION).tar.gz tmptar
	rm -rf tmptar

clean:
	rm -rf output/ tmptar
