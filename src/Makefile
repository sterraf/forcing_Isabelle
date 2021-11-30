OPTION  = -o parallel_proofs=2

CHAPTER = ZF

SESSION = Independence_of_CH

OUT_DIR = output/html

ML_FILES = Renaming_ML.ml Utils.ml 

DOC_FILES = root.tex root.bib root.bst

LINKING_DIR  = $(PWD)/../scripts
PARALLEL     = $(shell cat thy_files | egrep -v '^\#' | sed s/\.thy/\.html/g )
THY_FILES    = $(shell cat thy_files | egrep -v '^\#' | tr \" " ")
DOCU_FILES   = $(shell echo $(DOC_FILES) | sed "s_ _ document/_g" | \
	 sed "s_^_document/_g")
USR_HEAPS    = $(shell isabelle getenv -b ISABELLE_HEAPS)
ML_ID        = $(shell isabelle getenv -b ML_IDENTIFIER)
HEAP_LOG_DIR = $(USR_HEAPS)/$(ML_ID)/log
HTML_DIR     = $(OUT_DIR)/$(CHAPTER)/$(SESSION)
DB           = $(HEAP_LOG_DIR)/$(SESSION).db 
NEWTEMP      = 0

.PHONY: build html tar clean afp debug linked

$(DB):	thy_files $(THY_FILES) $(ML_FILES) $(DOCU_FILES) ROOT
	isabelle build $(OPTION) -v -c -d . $(SESSION)

build: 	$(DB)

$(HTML_DIR):	thy_files $(THY_FILES) $(ML_FILES) ROOT \
		$(DOCU_FILES)
	isabelle env \
	   ISABELLE_BROWSER_INFO=$(OUT_DIR)\
	   isabelle build $(OPTION) -d . -c -o browser_info -v $(SESSION)

html:	$(HTML_DIR)

html_linked:	$(HTML_DIR)  $(LINKING_DIR)
	rm -rf html_linked
	if [ ! -d tmphtml ]; then mkdir tmphtml; else rm -rf tmphtml/html_linked; fi
	/bin/cp -fr $(HTML_DIR) tmphtml/html_linked
	sh $(LINKING_DIR)/fix_links.sh  tmphtml/html_linked
	cat $(LINKING_DIR)/links.css >> tmphtml/html_linked/isabelle.css
	cp locale_assumptions_$(SESSION).txt tmphtml/html_linked
	cd tmphtml/html_linked; \
	 	bash $(LINKING_DIR)/parsing.sh $(SESSION); \
	 	bash $(LINKING_DIR)/linking.sh $(SESSION) . . $(PARALLEL)
	rsync -ah --exclude 'sed*' tmphtml/html_linked .

$(SESSION).tar.gz:	$(HTML_DIR) Makefile_distro ROOT README.md
	rm -rf tmptar
	mkdir tmptar
	mkdir tmptar/src
	cp README.md tmptar
	cp -r $(LINKING_DIR) tmptar/
	cp -r README.md thy_files $(THY_FILES) $(ML_FILES)\
	 ROOT document/ tmptar/src
	cp Makefile_distro tmptar/src/Makefile
	 ## Avoid temporary sed files from linking:
	rsync -ah --exclude 'sed*' $(HTML_DIR)/ tmptar/html
	tar --transform "s/tmptar/$(SESSION)/g" --show-transformed-names\
	 -cvzf $(SESSION).tar.gz tmptar
	rm -rf tmptar

tar:    $(SESSION).tar.gz

linked:	html_linked $(LINKING_DIR)/linking.sh Makefile_distro ROOT README.md
	rm -rf tmptar
	mkdir tmptar
	mkdir tmptar/src
	if [ ! -d tmphtml ]; then mkdir tmphtml; fi
	/bin/cp -fr html_linked tmphtml
	cd tmphtml/html_linked; \
		bash $(LINKING_DIR)/linking.sh ZF $(PWD)/../zf_item_lists/ \
		 https://cs.famaf.unc.edu.ar/~pedro/forcing/Forcing/ZF $(PARALLEL); \
		bash $(LINKING_DIR)/linking.sh ZF-Constructible $(PWD)/../zf_item_lists/ \
		 https://cs.famaf.unc.edu.ar/~pedro/forcing/Forcing/ZF-Constructible $(PARALLEL)
	cp README.md tmptar
	cp -r $(LINKING_DIR) tmptar/
	cp -r README.md thy_files $(THY_FILES) $(ML_FILES)\
		ROOT document/ tmptar/src
	cp Makefile_distro tmptar/src/Makefile
	## Avoid temporary sed files from linking:
	rsync -ah --exclude 'sed*' tmphtml/html_linked tmptar/
	tar --transform "s/tmptar/$(SESSION)/g" --show-transformed-names\
	 -cvzf $(SESSION).tar.gz tmptar
	rm -rf tmptar

$(SESSION)-AFP.tar.gz:    thy_files $(THY_FILES) $(ML_FILES) ROOT_AFP $(DOCU_FILES)
	rm -rf tmpafp
	mkdir tmpafp
	cp $(THY_FILES) $(ML_FILES) tmpafp
	cp ROOT_AFP tmpafp/ROOT
	cp -r document/ tmpafp
	tar --transform "s/tmpafp/$(SESSION)/g" --show-transformed-names\
	 -cvzf $(SESSION)-AFP.tar.gz tmpafp

afp:	$(SESSION)-AFP.tar.gz

clean:
	rm -rf output/ tmptar tmpafp html_linked
debug:
	@echo "================================="
	@echo "Arguments:"
	@echo
	@echo "OPTION  = "$(OPTION)
	@echo "CHAPTER = "$(CHAPTER)
	@echo "SESSION = "$(SESSION)
	@echo "OUT_DIR = "$(OUT_DIR)
	@echo "ML_FILES  ="$(ML_FILES)
	@echo "================================="
	@echo "Automatic values:"
	@echo
	@echo "LINKING_DIR  = "$(LINKING_DIR)
	@echo "PARALLEL     = "$(PARALLEL)
	@echo "THY_FILES    = "$(THY_FILES)
	@echo "DOCU_FILES   = "$(DOCU_FILES)
	@echo "USR_HEAPS    = "$(USR_HEAPS)
	@echo "ML_ID        = "$(ML_ID)
	@echo "HEAP_LOG_DIR = "$(HEAP_LOG_DIR)
	@echo "HTML_DIR     = "$(HTML_DIR)
	@echo "DB           = "$(DB)
