The Independence of the CH in Isabelle/ZF
=========================================

We redeveloped our formalization of forcing in the set theory framework of
Isabelle/ZF. Under the assumption of the existence of a countable
transitive model of ZFC, we construct proper generic extensions
that satisfy the Continuum Hypothesis and its negation.

The source theory files are located in the `src` directory.

An HMTL version can be found at
https://cs.famaf.unc.edu.ar/~pedro/forcing/Independence_CH/


Running the session with jEdit
==============================

The session can be run using the standard Isabelle IDE by
executing
```
$ isabelle jedit -l Transitive_Models -d . Definitions_Main.thy
```
at the `src` directory.

Building the session
====================

To build (check) the session, execute
```
$ cd $FORCING_HOME/src
$ make build
```

System requirements
===================

The session requires Isabelle2021-1 (https://isabelle.in.tum.de/website-Isabelle2021-1/index.html)
to be installed with the AFP component loaded (by downloading from
https://www.isa-afp.org/download.html and following the instructions at https://www.isa-afp.org/using.html).
The tool wrapper 'isabelle' should be on the `PATH` env var.


E. Gunther, M. Pagano, P. Sánchez Terraf, M. Steinberg (2022)
