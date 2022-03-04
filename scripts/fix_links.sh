#!/bin/bash
old_dir=$PWD
html_dir="$1"

cd $html_dir
sed -i -- 's|a href="../ZF/|a href="https://www.cl.cam.ac.uk/research/hvg/Isabelle/dist/library/ZF/ZF/|g' *.html
sed -i -- 's|a href="../ZF-Constructible/|a href="https://www.cl.cam.ac.uk/research/hvg/Isabelle/dist/library/ZF/ZF-Constructible/|g' *.html
sed -i -- 's|a href="../../AFP/|a href="https://www.isa-afp.org/browser_info/current/AFP/|g' *.html
cd $old_dir
