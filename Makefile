# uncomment for profiling builds
# PROF=defined
# DEBUG=defined

fgl-control-order-dependence.cabal : fgl-control-order-dependence.cabal.m4
	m4 $< > $@

ifdef PROF
CABAL_CONFIGURE=--enable-library-profiling --enable-executable-profiling --ghc-options="-fprof-auto"
else ifdef DEBUG
CABAL_CONFIGURE=--enable-library-profiling --enable-executable-profiling --ghc-options="-fno-ignore-asserts"
else 
CABAL_CONFIGURE=                                                         --ghc-options="-fno-ignore-asserts"
endif

PATTERN=
COLOR=--color always
RTS=

LOCK=dotlockfile -l -r 200 ghc-lock
UNLOCK=dotlockfile -u      ghc-lock

# all.test giffhorn.test cdom.test balanced.test timing.test soundness.test all should be .PHONY targets here, but the pattern rules below dont like that
.PHONY: all  rofl .FORCE
.PRECIOUS: dist/build/%.bin

all : all.test all.fail

%.xml : %.xml.bin
	touch $@
	./$< $(RTS) $(PATTERN) --xml $@

dist/build/%.bin : fgl-control-order-dependence.cabal .FORCE
	$(LOCK)
	-cabal configure $(CABAL_CONFIGURE) && cabal build $(@F)
	$(UNLOCK)



%.xml.fixed.xml : %.xml flatten-testsuite.xslt
	cat $< | xmllint --format - | saxon-xslt /dev/stdin flatten-testsuite.xslt  > $@

clean :
	cabal clean
	find -name "*.prof"    -not -path "./.cabal-sandbox/*" -delete
	find -name "*.dot"     -not -path "./.cabal-sandbox/*" -delete
	find -name "*~"        -not -path "./.cabal-sandbox/*" -delete

expand = $1

.SECONDEXPANSION:
unitTestReports/%.xml.fixed.xml/html/index.html : $$(call expand, dist/build/$$*.xml.bin/$$*.xml.fixed.xml) .FORCE
	ant -v -buildfile test-xml-to-html.xml -Dxmlfile=$<

unitTestReports/%.xml/html/index.html : $$(call expand, dist/build/$$*.xml.bin/$$*.xml) .FORCE
	ant -v -buildfile test-xml-to-html.xml -Dxmlfile=$<


%.run : $$(call expand, dist/build/$$*.bin/$$*.bin) .FORCE
	./$< $(RTS) $(PATTERN) $(COLOR)
