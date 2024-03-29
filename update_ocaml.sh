#!/bin/bash

#to_copy.txt contains relative paths of files to copy : ex: core/ty.ml
FILES="to_copy.txt"
#TODO: PATH variable?
TGT=/home/josh/Documents/why3_big/why3-test

if [ -z "$1" ]; then
	echo "Updating files:"
    ARG=false
  elif [ "$1" = "--comp" ]; then
  	echo "Showing differences:"
  	ARG=true
  else
  	echo "Unknown option: "$1
  	exit 0
fi

#iterate through lines in file
while read p; do
	#get old filename
	SRCFILE=$(basename "$p")
	#get old file
	SRC=_build/default/extract/$SRCFILE
	#get destination
	DST=$TGT/src/$p
	#if SRC is newer than DST, replace
	if cmp --silent -- "$SRC" "$DST"; then
		:
	else
	  #If we select the --comp option, just print different files
	  if [ "$ARG" = "true" ]; then
	  	echo "$p"
	  else
	    rm -f $DST
	    cp $SRC $DST
	    echo "Updated "$p$
	  fi
	fi
done < $FILES
