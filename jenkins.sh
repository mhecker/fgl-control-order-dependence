#!/bin/bash
shopt -s expand_aliases
set -x
timm() {
  /usr/bin/time -f '\t%E real,\t%U user,\t%S sys,\t%K amem,\t%M mmem' "$@"
}
export -f timm

set +e
make fgl-control-order-dependence.cabal
make clean
cabal install --only-dependencies
parallel --delay 120 --jobs 8 < jenkins_parallel.sh
timm             make dist/build/sensitiveDom.valid.xml.bin/sensitiveDom.valid.xml     RTS="+RTS -M22288m     -RTS" PATTERN="-p '**/Properties/**'"
timm             make dist/build/all.invalid.xml.bin/all.invalid.xml                   RTS="+RTS -M22288m -N8 -RTS"
