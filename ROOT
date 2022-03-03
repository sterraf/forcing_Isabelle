chapter "ZF"

session "Transitive_Models" in "." =  "Delta_System_Lemma" +
  description "
    Transitive Models of Fragments of ZFC

    We extend the ZF-Constructibility library by relativizing theories
    of the Isabelle/ZF and Delta System Lemma sessions to a transitive
    class. We also relativize Paulson's work on Aleph and our former
    treatment of the Axiom of Dependent Choices. This work is a
    prerrequisite to our formalization of the independence of the
    Continuum Hypothesis.
  "
  options [timeout=180, document = pdf, document_output = "output",
	   document_variants = "document:outline=/proof,/ML"]
  theories
    "Renaming_Auto"
    "Delta_System_Relative"
    "Partial_Functions_Relative"
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
