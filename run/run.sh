#!/bin/bash


OPERATION="../cbp3 -t"
SUFFIX=txt # log extension

if [ -n "$1" ]
then
  directory=$1      # If directory name given as a script argument...
else
  directory=$PWD    # Otherwise use current working directory.
fi  
  

for file in $directory/traces/*.bz2    # Filename globbing.
do
  filename=${file%.bz2}      #  Strip ".bz2" suffix off filename
  filename=${filename#$directory/traces/}      #  Strip "$directory/traces/" prefix off filename
                          
  $OPERATION $file > "$directory/outputs/$filename.$SUFFIX"
  echo "$filename.$SUFFIX"  # Log what is happening to stdout.
done

exit 0

