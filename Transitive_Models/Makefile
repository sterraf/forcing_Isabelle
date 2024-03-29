OPTION  = -o parallel_proofs=1

CHAPTER = ZF

SESSION = Transitive_Models

OUT_DIR = output/html

DOC_FILES = root.tex root.bib root.bst

LINKING_DIR  = $(PWD)/../scripts
FULL_DEPS    = $(shell isabelle build -l -n -d . $(SESSION) | grep "^  ")
LOCAL_FILES  = $(shell isabelle build -l -n -d . $(SESSION) | grep $(PWD) | grep -v "document/")
DOCU_FILES   = $(shell echo $(DOC_FILES) | sed "s_ _ document/_g" | \
	 sed "s_^_document/_g")
USR_HEAPS    = $(shell isabelle getenv -b ISABELLE_HEAPS)
ML_ID        = $(shell isabelle getenv -b ML_IDENTIFIER)
HEAP_LOG_DIR = $(USR_HEAPS)/$(ML_ID)/log
HTML_DIR     = $(OUT_DIR)/$(CHAPTER)/$(SESSION)
DB           = $(HEAP_LOG_DIR)/$(SESSION).db 

.PHONY: build html tar clean afp debug linked

$(DB):	$(FULL_DEPS) $(DOCU_FILES) ROOT
	isabelle build $(OPTION) -v -c -d . $(SESSION)

build: 	$(DB)

$(HTML_DIR):	$(LOCAL_FILES)  ROOT \
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
	rsync -ah --exclude 'sed*' tmphtml/html_linked .

linked: html_linked

$(SESSION).tar.gz:	html_linked Makefile_distro ROOT README.md
	rm -rf tmptar
	mkdir tmptar
	mkdir tmptar/src
	cp README.md tmptar
	# cp -r $(LINKING_DIR) tmptar/
	cp -r README.md $(LOCAL_FILES) \
	 ROOT tmptar/src
	cp Makefile_distro tmptar/src/Makefile
	mkdir tmptar/src/document
	cp -r $(DOCU_FILES) tmptar/src/document
	 ## Avoid temporary sed files from linking:
	rsync -ah --exclude 'sed*' html_linked/ tmptar/html
	tar --transform "s/tmptar/$(SESSION)/g" --show-transformed-names\
	 -cvzf $(SESSION).tar.gz tmptar
	rm -rf tmptar

tar:    $(SESSION).tar.gz

$(SESSION)-AFP.tar.gz:    $(LOCAL_FILES)  ROOT_AFP $(DOCU_FILES)
	rm -rf tmpafp
	mkdir tmpafp
	cp $(LOCAL_FILES) tmpafp
	cp ROOT_AFP tmpafp/ROOT
	mkdir tmpafp/document
	cp -r $(DOCU_FILES) tmpafp/document
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
	@echo "================================="
	@echo "Automatic values:"
	@echo
	@echo "LINKING_DIR  = "$(LINKING_DIR)
	@echo "LOCAL_FILES    = "$(LOCAL_FILES)
	@echo "DOCU_FILES   = "$(DOCU_FILES)
	@echo "USR_HEAPS    = "$(USR_HEAPS)
	@echo "ML_ID        = "$(ML_ID)
	@echo "HEAP_LOG_DIR = "$(HEAP_LOG_DIR)
	@echo "HTML_DIR     = "$(HTML_DIR)
	@echo "DB           = "$(DB)
