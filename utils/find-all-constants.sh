#!/bin/bash

list="$2"

while :
do
  # echo "./souper-check $1 -infer-const -infer-const-only-print-consts -infer-const-blocklist="$list" | grep $2 | awk '{print \$2}'"
  # ./souper-check $1 -infer-const -infer-const-only-print-consts -infer-const-blocklist=$list
  cur=`./souper-check $1 -infer-const -infer-const-only-print-consts -infer-const-blocklist="$list" | grep $2 | awk '{print \$2}'`

  # trick to test if a string is a number
  if [ -n "$cur" ] && [ "$cur" -eq "$cur" ] 2>/dev/null; then
    list="$list,$cur"
    echo $list
    echo $list | gawk -F',' '{ for(i=2; i<=NF; i++) printf "0x%02x,", $i }' | sed 's/,$//'
    echo
  else
    break
  fi
done
