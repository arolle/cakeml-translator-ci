#!/usr/bin/env bash

# usage: CAKEMLDIR=... ./cakeml_hol_deps.sh
# calculate the prerequisites of CakeML

grep --no-filename --recursive --include=Holmakefile HOLDIR $CAKEMLDIR |
  sed 's/ /\n/g;s/\\$//g' |
  grep HOLDIR |
  grep --invert-match 'HOLHEAP\|bin/buildheap' |
  grep --invert-match 'mips\|arm\|riscv\|x64' |
  awk '{$1=$1};1' | sed 's/\$(HOLDIR)\///g' | sort | uniq

