#!/bin/bash

#to_copy.txt contains relative paths of files to copy : ex: core/ty.ml
FILES="to_copy.txt"
#TODO: PATH variable?
TGT=/home/josh/Documents/why3_big/why3-test

#iterate through lines in file
while read p; do
	#get old filename
	SRCFILE=$(basename "$p")
	#get old file
	SRC=_build/default/extract/$SRCFILE
	#get destination
	DST=$TGT/src/$p
	#echo "$p"
	#echo "$SRC"
	#echo "$DST"
	#if SRC is newer than DST, replace
	if cmp --silent -- "$SRC" "$DST"; then
		:
	else
	  rm -f $DST
	  cp $SRC $DST
	  echo "Updated "$p$
	# else
	#   echo "files differ"
	# fi
	# if [[ $SRC -nt $DST ]]; then
	#   rm $DST
	#   cp $SRC $DST
	#   echo "Updated "$p$
	fi
done < $FILES
