#!/bin/bash
old_dir=$PWD
html_dir="output/html/ZF/Forcing/"

cd $html_dir
sed -i -- 's/a href="..\/ZF\/ZF.html/a href="https:\/\/www.cl.cam.ac.uk\/research\/hvg\/Isabelle\/dist\/library\/ZF\/ZF\/ZF.html/g' *.html
sed -i -- 's/a href="..\/ZF\/ZF\//a href="https:\/\/www.cl.cam.ac.uk\/research\/hvg\/Isabelle\/dist\/library\/ZF\/ZF\//g' *.html
#sed -i -- 's/a href="..\/ZF\/ZF-Constructible\//a href="https:\/\/www.cl.cam.ac.uk\/research\/hvg\/Isabelle\/dist\/library\/ZF\/ZF-Constructible\//g' *.html
cd $old_dir
