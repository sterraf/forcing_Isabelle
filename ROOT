chapter "ZF"

session "Transitive_Models" in "." =  "Delta_System_Lemma" +
  description "
    Transitive Models of Fragments of ZFC

    We extend Paulson's ZF-Constructible library obtaining relative
    versions of most of the theories appearing in the ZF session.
  "
  options [timeout=500, document = pdf, document_output = "output",
	   document_variants = "document:outline=/proof,/ML"]
  theories
    "Renaming_Auto"
    "Delta_System_Relative"
    "Pointed_DC_Relative"
  document_files
    "root.tex"
    "root.bib"
    "root.bst"

session "Independence_CH" in "Indep_CH" =  "Transitive_Models" +
  description "
    The Independence of the Continuum Hypothesis

    We redeveloped our formalization of forcing in the set theory framework of
    Isabelle/ZF. Under the assumption of the existence of a countable 
    transitive model of ZFC, we construct proper generic extensions 
    that satisfy the Continuum Hypothesis and its negation.
  "  
  options [timeout=500, document = pdf, document_output = "output",
  	   document_variants = "document:outline=/proof,/ML"]
  theories
    "Definitions_Main"
  document_files
    "root.tex"
    "root.bib"
    "root.bst"
