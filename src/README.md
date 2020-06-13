Forcing in Isabelle/ZF
======================

The source theory files are located in the `src` directory.
The directory `html` contains a browseable and cross-linked
version of the sources.

Running the session with jEdit
==============================

The session can be run using the standard Isabelle IDE by
executing
```
$ isabelle jedit -d . Forcing_Main.thy
```
in the `src` directory. 


Building the session
====================

To build (check) the session, change to 'src' and run
```
$ make build
```

To obtain also an HTML version of the sources, do
```
$ make html
```

To make a tar, run
```
$ make tar
```

System requirements
===================

The session requires Isabelle2020 to be installed, and the
tool wrapper 'isabelle' should be on the `PATH` env var.

At least 8G of RAM would be desirable. If memory 
requirements are not met, there is a chance that the 
building process stalls indefinitely at some point, without
failing.


E. Gunther, M. Pagano, P. Sánchez Terraf (2020)