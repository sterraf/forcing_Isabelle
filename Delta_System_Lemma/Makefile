OPTION  = -o parallel_proofs=1

CHAPTER = ZF

SESSION = Delta_System_Lemma

OUT_DIR = output/html

ML_FILES  =

DOC_FILES = root.tex root.bib root.bst    header-delta-system.tex \
	multidef.sty

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

.PHONY: build html tar clean afp debug

$(DB):	thy_files $(THY_FILES) $(ML_FILES) Makefile $(DOCU_FILES) ROOT
	isabelle build $(OPTION) -v -c -d . $(SESSION)

build: 	$(DB)

$(HTML_DIR):	thy_files $(THY_FILES) $(ML_FILES) $(LINKING_DIR) ROOT \
		$(DOCU_FILES) Makefile
	isabelle env \
	  ISABELLE_BROWSER_INFO=$(OUT_DIR)\
	  isabelle build $(OPTION) -d . -c -o browser_info -v $(SESSION)
	sh $(LINKING_DIR)/fix_links.sh  $(SESSION) $(CHAPTER) $(OUT_DIR)
	cat $(LINKING_DIR)/links.css >> $(HTML_DIR)/isabelle.css
	cp locale_assumptions_$(SESSION).txt $(HTML_DIR)
	cd $(HTML_DIR); \
		bash $(LINKING_DIR)/parsing.sh $(SESSION); \
		bash $(LINKING_DIR)/linking.sh $(SESSION) . . $(PARALLEL)

html:	$(HTML_DIR)

$(SESSION).tar.gz:	$(HTML_DIR) ROOT README.md
	rm -rf tmptar
	mkdir tmptar
	mkdir tmptar/src
	cp README.md tmptar
	cp -r $(LINKING_DIR) tmptar/
	cp -r README.md thy_files $(THY_FILES) $(ML_FILES)\
	 ROOT document/ tmptar/src
	cp Makefile tmptar/src/
	 ## Avoid temporary sed files from linking:
	rsync -ah --exclude 'sed*' $(HTML_DIR)/ tmptar/html
	tar --transform "s/tmptar/$(SESSION)/g" --show-transformed-names\
	 -cvzf $(SESSION).tar.gz tmptar
	rm -rf tmptar

tar:    $(SESSION).tar.gz

linked:	$(HTML_DIR) $(LINKING_DIR)/linking.sh ROOT README.md
	rm -rf tmptar
	mkdir tmptar
	mkdir tmptar/src
	cd $(HTML_DIR); \
		bash $(LINKING_DIR)/linking.sh ZF $(PWD)/../zf_item_lists/ \
		 https://cs.famaf.unc.edu.ar/~pedro/forcing/Forcing/ZF $(PARALLEL); \
		bash $(LINKING_DIR)/linking.sh ZF-Constructible $(PWD)/../zf_item_lists/ \
		 https://cs.famaf.unc.edu.ar/~pedro/forcing/Forcing/ZF-Constructible $(PARALLEL)
	cp README.md tmptar
	cp -r $(LINKING_DIR) tmptar/
	cp -r README.md thy_files $(THY_FILES) $(ML_FILES)\
	 ROOT document/ tmptar/src
	cp Makefile tmptar/src/
	 ## Avoid temporary sed files from linking:
	rsync -ah --exclude 'sed*' $(HTML_DIR)/ tmptar/html
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
	rm -rf output/ tmptar tmpafp
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
