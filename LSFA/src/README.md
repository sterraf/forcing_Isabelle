*** First steps toward a formalization of Forcing ***

Authors:
- Gunther, Emmanuel
- Pagano, Miguel
- Sánchez Terraf, Pedro

This development corresponds to the formalization of 
concepts of Forcing, submitted in LSFA 2018.

This README file contains description of the source files.

** Isabelle **

The formalization was tested on Ubuntu with Isabelle2016.
You can download this version of Isabelle from here:

https://isabelle.in.tum.de/website-Isabelle2016-1/index.html


** Modules **

The formalization is modularized in these files:


- Pointed_DC
	Proof of a version of the Axiom of Choice:
	the Principle of Dependent Choices.
- Forcing_notions.thy
	Definition of forcing notions: preorders with top,
	dense subsets, generic filters. Proof of the
	Rasiowa-Sikorski theorem.
- Forcing_data.thy
	Definition of locale forcing_data: A transitive and countable
	set containing the preorder with top.
	Proof of the existence of a generic filter.
- Names.thy
	Definition of Generic extension of a model M of ZFC: M[G].
	Definition of function val and check, and properties about 
	them. Proof that G belongs to M[G] and that the latter is
	a transitive set.
- Gen_ext_pair.thy
	Proof of the axiom of Pairing in the generic
	extension M[G].
