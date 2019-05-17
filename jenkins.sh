set +e
make fgl-control-order-dependence.cabal
make clean
cabal install --only-dependencies
time             make dist/build/all.valid.xml.bin/all.valid.xml                       RTS="+RTS -M22288m -RTS" PATTERN="-p '**/Unit tests/**'"
time             make dist/build/cdom.valid.xml.bin/cdom.valid.xml                     RTS="+RTS -M22288m -RTS" PATTERN="-p '**/Properties/**'"
time             make dist/build/balanced.valid.xml.bin/balanced.valid.xml             RTS="+RTS -M22288m -RTS" PATTERN="-p '**/Properties/**'"
time             make dist/build/timing.valid.xml.bin/timing.valid.xml                 RTS="+RTS -M22288m -RTS" PATTERN="-p '**/Properties/**'"
time             make dist/build/timingDep.valid.xml.bin/timingDep.valid.xml           RTS="+RTS -M22288m -RTS" PATTERN="-p '**/Properties/**'"
time             make dist/build/simon.valid.xml.bin/simon.valid.xml                   RTS="+RTS -M22288m -RTS" PATTERN="-p '**/Properties/**'"
time             make dist/build/giffhorn.valid.xml.bin/giffhorn.valid.xml             RTS="+RTS -M22288m -RTS" PATTERN="-p '**/Properties/**'"
time             make dist/build/preccex.valid.xml.bin/preccex.valid.xml               RTS="+RTS -M22288m -RTS" PATTERN="-p '**/Properties/**'"
time             make dist/build/nticd.valid.xml.bin/nticd.valid.xml                   RTS="+RTS -M22288m -RTS" PATTERN="-p '**/Properties/**'"
time             make dist/build/ntscd.valid.xml.bin/ntscd.valid.xml                   RTS="+RTS -M22288m -RTS" PATTERN="-p '**/Properties/**'"
time             make dist/build/newcd.valid.xml.bin/newcd.valid.xml                   RTS="+RTS -M22288m -RTS" PATTERN="-p '**/Properties/**'"
time             make dist/build/dod.valid.xml.bin/dod.valid.xml                       RTS="+RTS -M22288m -RTS" PATTERN="-p '**/Properties/**'"
time             make dist/build/wod.valid.xml.bin/wod.valid.xml                       RTS="+RTS -M22288m -RTS" PATTERN="-p '**/Properties/**'"
time             make dist/build/color.valid.xml.bin/color.valid.xml                   RTS="+RTS -M22288m -RTS" PATTERN="-p '**/Properties/**'"
time             make dist/build/reducible.valid.xml.bin/reducible.valid.xml           RTS="+RTS -M22288m -RTS" PATTERN="-p '**/Properties/**'"
time             make dist/build/indeps.valid.xml.bin/indeps.valid.xml                 RTS="+RTS -M22288m -RTS" PATTERN="-p '**/Properties/**'"
time timeout 60m make dist/build/delay.valid.xml.bin/delay.valid.xml                   RTS="+RTS -M22288m -RTS" PATTERN="-p '**/Properties/**'"
time             make dist/build/insensitiveDom.valid.xml.bin/insensitiveDom.valid.xml RTS="+RTS -M22288m -RTS" PATTERN="-p '**/Properties/**'"
time             make dist/build/sensitiveDom.valid.xml.bin/sensitiveDom.valid.xml     RTS="+RTS -M22288m -RTS" PATTERN="-p '**/Properties/**'"
time             make dist/build/misc.valid.xml.bin/misc.valid.xml                     RTS="+RTS -M22288m -RTS" PATTERN="-p '**/Properties/**'"
time timeout 60m make dist/build/soundness.valid.xml.bin/soundness.valid.xml           RTS="+RTS -M22288m -RTS" PATTERN="-p '**/Properties/**'"

time             make dist/build/all.invalid.xml.bin/all.invalid.xml                   RTS="+RTS -M22288m -RTS"
