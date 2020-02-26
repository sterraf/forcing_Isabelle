OPTION = -o parallel_proofs=1

CHAPTER = ZF

SESSION = Delta_System_Lemma

OUT_DIR = output/html

ML_FILES = 

LINKING_DIR  = ../scripts
PARALLEL     = $(shell cat thy_files | sed s/\.thy/\.html/g )
THY_FILES    = $(shell cat thy_files | tr \" " ")
USR_HEAPS    = $(shell isabelle getenv ISABELLE_HEAPS | cut -f2 -d"=")
ML_ID        = $(shell isabelle getenv ML_IDENTIFIER | cut -f2 -d"=")
HEAP_LOG_DIR = $(USR_HEAPS)/$(ML_ID)/log
HTML_DIR     = $(OUT_DIR)/$(CHAPTER)/$(SESSION)
DB           = $(HEAP_LOG_DIR)/$(SESSION).db 

.PHONY: build html tar clean

$(DB):	$(THY_FILES) $(ML_FILES)
	isabelle build $(OPTION) -v -c -d . $(SESSION)

build: 	$(DB)

$(HTML_DIR):	$(THY_FILES) $(ML_FILES) $(LINKING_DIR) ROOT
	isabelle env \
	  ISABELLE_BROWSER_INFO=$(OUT_DIR)\
	  isabelle build $(OPTION) -d . -c -o browser_info -v $(SESSION)
	sh $(LINKING_DIR)/fix_links.sh  $(SESSION) $(CHAPTER) $(OUT_DIR)
	cat $(LINKING_DIR)/links.css >> $(HTML_DIR)/isabelle.css

html:	$(HTML_DIR)

$(SESSION).tar.gz:	$(HTML_DIR) ../scripts/link-html.sh Makefile ROOT
	time bash $(LINKING_DIR)/link-html.sh $(SESSION) $(CHAPTER) $(OUT_DIR) $(PARALLEL)
	rm -rf tmptar
	mkdir tmptar
	mkdir tmptar/src
	cp README tmptar
	cp -r $(LINKING_DIR) tmptar/
	cp -r README $(PARALLELIZATION) thy_files $(THY_FILES) $(ML_FILES)\
	 ROOT document/ tmptar/src
	cp Makefile tmptar/src/
	 ## Avoid temporary sed files from linking:
	rsync -ah --exclude 'sed*' $(HTML_DIR)/ tmptar/html
	tar --transform "s/tmptar/$(SESSION)/g" --show-transformed-names\
	 -cvzf $(SESSION).tar.gz tmptar
	rm -rf tmptar

tar:    $(SESSION).tar.gz

clean:
	rm -rf output/ tmptar
