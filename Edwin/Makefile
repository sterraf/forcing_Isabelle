ML_FILES =

OPTION = -o parallel_proofs=1

# LINKING_FILES = fix_links.sh links.css

CHAPTER = ZF

SESSION = Delta_System_Lemma

OUT_DIR = output/html

THY_FILES  = $(shell cat thy_files)
USR_HEAPS  = $(shell isabelle getenv ISABELLE_HEAPS | cut -f2 -d"=")
ML_ID      = $(shell isabelle getenv ML_IDENTIFIER | cut -f2 -d"=")
HEAP_LOG_DIR = $(USR_HEAPS)/$(ML_ID)/log
HTML_DIR   = $(OUT_DIR)/$(CHAPTER)/$(SESSION)
DB         = $(HEAP_LOG_DIR)/$(SESSION).db 

.PHONY: build html tar clean

$(DB):	$(THY_FILES) $(ML_FILES)
	isabelle build $(OPTION) -v -c -d . $(SESSION)

build: 	$(DB)

$(HTML_DIR):	$(THY_FILES) $(ML_FILES) $(LINKING_FILES)
	isabelle env \
	  ISABELLE_BROWSER_INFO=$(OUT_DIR)\
	  isabelle build $(OPTION) -d . -c -o browser_info -v $(SESSION)
	# sh fix_links.sh
	# cat links.css >> $(HTML_DIR)/isabelle.css

html:	$(HTML_DIR)

forcing.tar.gz:	$(HTML_DIR) link-forcing.sh Makefile_distro
	time bash link-forcing.sh
	rm -rf tmptar
	mkdir tmptar
	mkdir tmptar/src
	cp -r ../Constructible tmptar
	cp README tmptar
	cp -r $(THY_FILES) $(ML_FILES) $(LINKING_FILES) ROOT document/ tmptar/src
	cp Makefile_distro tmptar/src/Makefile
	cp -r $(HTML_DIR) tmptar/html
	tar --transform "s/tmptar/$(SESSION)/g" --show-transformed-names -cvzf forcing.tar.gz tmptar
	rm -rf tmptar

# tar:    forcing.tar.gz

clean:
	rm -rf output/ tmptar
