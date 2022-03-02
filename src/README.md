The Independence of the CH in Isabelle/ZF
=========================================

This is a development version. It is organized in two sessions:

  * `Transitive_Models` where we extend Paulson's `ZF-Constructible` library, and
  * `Independence_CH` (in the directory `src`) where we develop the theory of forcing.

An HMTL version can be found at
https://cs.famaf.unc.edu.ar/~pedro/forcing/Independence_CH/

Prerequisite
============
In order to edit/browse the session `Independence_CH` in jEdit you need 
to add the directory of `Transitive_Models` as a component (let us suppose
that $FORCING_HOME is the directory with `Transitive_Models` and `src`):
```
$ isabelle components -u $FORCING_HOME/Transitive_Models
```

Running the session with jEdit
==============================

The session can be run using the standard Isabelle IDE by
executing
```
$ cd $FORCING_HOME/src
$ isabelle jedit -l ZF-Constructible Definitions_Main.thy
```

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
