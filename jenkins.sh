set +e
make clean
time             make all.test.xml       THREADED="" RTS="+RTS -M22288m -RTS" PATTERN="-p '**/Unit tests/**'"
time             make nticd.test.xml     THREADED="" RTS="+RTS -M22288m -RTS" PATTERN="-p '**/Properties/**'"
time timeout 60m make ntscd.test.xml     THREADED="" RTS="+RTS -M22288m -RTS" PATTERN="-p '**/Properties/**'"
time             make misc.test.xml      THREADED="" RTS="+RTS -M22288m -RTS" PATTERN="-p '**/Properties/**'"
time timeout 60m make cdom.test.xml      THREADED="" RTS="+RTS -M22288m -RTS" PATTERN="-p '**/Properties/**'"
time timeout 60m make timing.test.xml    THREADED="" RTS="+RTS -M22288m -RTS" PATTERN="-p '**/Properties/**'"
time             make giffhorn.test.xml  THREADED="" RTS="+RTS -M22288m -RTS" PATTERN="-p '**/Properties/**'"
time             make preccex.test.xml   THREADED="" RTS="+RTS -M22288m -RTS" PATTERN="-p '**/Properties/**'"
time             make balanced.test.xml  THREADED="" RTS="+RTS -M22288m -RTS" PATTERN="-p '**/Properties/**'"
time             make simon.test.xml     THREADED="" RTS="+RTS -M22288m -RTS" PATTERN="-p '**/Properties/**'"
time timeout 60m make all.fail.xml       THREADED="" RTS="+RTS -M22288m -RTS"
time timeout 60m make soundness.test.xml THREADED="" RTS="+RTS -M22288m -RTS" PATTERN="-p '**/Properties/**'"
