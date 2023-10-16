#!/bin/bash
# Converts a file with multiple souper optimizations to a directory having one optimization per file
# $1 - file
# $2 - dir
rm $2/*
if [[ $OSTYPE == 'darwin'* ]]; then
  # Use macos csplit instead of gnu version?
  gcsplit --quiet --prefix=$2/opt --suffix-format=%02d.opt $1 '/^result/ +1' '{*}'
else
  csplit --quiet --prefix=$2/opt --suffix-format=%02d.opt $1 '/^result/ +1' '{*}'
fi
