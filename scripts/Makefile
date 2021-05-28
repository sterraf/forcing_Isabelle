ISADIR     = `isabelle getenv -b ISABELLE_HOME`

ZFDIR      = $(ISADIR)/src/ZF/output/html/ZF/ZF

CONSTRDIR  = $(ISADIR)/src/ZF/Constructible/output/html/ZF/ZF-Constructible

CSS        = $(ISADIR)/etc/isabelle.css

ITEMSDIR   = ../zf_item_lists
# relative to tmpdir/ZF, etc

PARALLELZF = $(shell cat $(ITEMSDIR)/parallel_ZF.txt)

PARALLELCONSTR = $(shell cat $(ITEMSDIR)/parallel_ZF-Constructible.txt)

.PHONY: ZF Constr index clean

ZF:	
	mkdir tmpdir
	cp -r $(ZFDIR) tmpdir
	cat links.css $(CSS) >> tmpdir/ZF/isabelle.css
	#touch tmpdir/ZF/locale_assumptions_ZF.txt
	cd tmpdir/ZF; \
		../../parsing.sh ZF; \
		../../linking.sh ZF . .  $(PARALLELZF)
	cd tmpdir; \
		rsync -ah --exclude 'sed*' ZF tmptar_ZF; \
		tar --transform "s/tmptar_ZF/ZF/g" --show-transformed-names\ -zcvf ZF.tar.gz tmptar_ZF

tmpdir/ZF-Constructible.tar.gz:	tmpdir/ZF.tar.gz
	cp -r $(CONSTRDIR) tmpdir
	cat links.css $(CSS) >> tmpdir/ZF-Constructible/isabelle.css
	cp $(ITEMSDIR)/locale_assumptions_ZF-Constructible.txt tmpdir/ZF-Constructible
	cd tmpdir/ZF-Constructible; \
		../../link_locales.sh ZF-Constructible . . $(PARALLELCONSTR);\
		../../parsing.sh ZF-Constructible; \
		../../linking.sh ZF ../ZF/ https://cs.famaf.unc.edu.ar/~pedro/forcing/Forcing/ZF $(PARALLELCONSTR); \
		../../linking.sh ZF-Constructible . . $(PARALLELCONSTR); \
	cd tmpdir; \
		## Avoid temporary sed files from linking:
		rsync -ah --exclude 'sed*' ZF-Constructible tmptar_CONST; \
		tar --transform "s/tmptar_CONST/ZF-Constructible/g" --show-transformed-names\ -zcvf ZF-Constructible.tar.gz tmptar_CONST

Constr:	tmpdir/ZF-Constructible.tar.gz

index:	tmpdir/ZF.tar.gz tmpdir/ZF-Constructible.tar.gz
	cd tmpdir; \
		cp ZF.tar.gz ZF-Constructible.tar.gz ..

clean:
	rm -rf tmpdir

clean-Constr:
	rm -rf tmpdir/ZF-Constructible tmpdir/ZF-Constructible.tar.gz tmpdir/tmptar_CONST
