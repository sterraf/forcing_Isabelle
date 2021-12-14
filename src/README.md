The Independence of the CH in Isabelle/ZF
=========================================

This is a development version.

The source theory files are located in the `src` directory.

An HMTL version can be found at
https://cs.famaf.unc.edu.ar/~pedro/forcing/Independence_CH/


Running the session with jEdit
==============================

The session can be run using the standard Isabelle IDE by
executing
```
$ isabelle jedit -l Delta_System_Lemma Definitions_Main.thy
```
at the `src` directory.


Building the session
====================

To build (check) the session, change to 'src' and run
```
$ make build
```

System requirements
===================

The session requires Isabelle2021 (https://isabelle.in.tum.de/website-Isabelle2021/index.html)
to be installed with the AFP component loaded (by downloading from
https://www.isa-afp.org/download.html and following the instructions at https://www.isa-afp.org/using.html).
The tool wrapper 'isabelle' should be on the `PATH` env var.


E. Gunther, M. Pagano, P. Sánchez Terraf, M. Steinberg (2021)
