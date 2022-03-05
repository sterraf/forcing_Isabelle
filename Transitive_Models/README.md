Transitive Models of Fragments of ZFC
=====================================

We extend the Paulson's `ZF-Constructibility` by relativizing theories
of the Isabelle/ZF and Delta System Lemma (AFP) sessions to a transitive
class. We also relativize Paulson's work on Aleph and our former
treatment of the Axiom of Dependent Choices. This work is a
prerequisite to our formalization of the independence of the
Continuum Hypothesis.

The source theory files are located in the `src` directory.

An HMTL version can be found at
https://cs.famaf.unc.edu.ar/~pedro/forcing/Transitive_Models/

Running the session with jEdit
==============================

The session can be run using the standard Isabelle IDE by
executing
```
$ isabelle jedit -d . -l ZF-Constructible Delta_System_Relative.thy
```

at the `src` directory. There are 3 other “leaves” of
the dependency graph (`Renaming_Auto.thy`,
`Partial_Functions_Relative.thy`, and `Pointed_DC_Relative.thy`) which
will not be checked unless they're opened explicitly, or the session
is built according to the following instructions.


Building the session
====================

To build (check) the session, execute
```
$ make build
```

System requirements
===================

The session requires Isabelle2021-1 (https://isabelle.in.tum.de/website-Isabelle2021-1/index.html)
to be installed with the AFP component loaded (by downloading from
https://www.isa-afp.org/download.html and following the instructions at https://www.isa-afp.org/using.html).
The tool wrapper 'isabelle' should be on the `PATH` env var.


E. Gunther, M. Pagano, P. Sánchez Terraf, M. Steinberg (2022)
