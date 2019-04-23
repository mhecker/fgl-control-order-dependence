# uncomment for profiling builds
# PROF=defined
# DEBUG=defined

#VALID=Program.Properties.ValidProperties
VALID=Program.Properties.SASProperties
INVALID=Program.Properties.InvalidProperties

ifdef PROF
PROF_GHC=-prof -fprof-auto -osuf p_o
PROF_RTS=-p
GHC_ASSERT=
else
GHC_ASSERT=-fno-ignore-asserts
endif

ifdef DEBUG
DEBUG_GHC=-prof -fprof-auto -fprof-cafs -osuf p_o
DEBUG_RTS=-xc
endif


THREADED=-threaded
RTS=+RTS $(PROF_RTS) $(DEBUG_RTS) -RTS
COLOR=--color always
ROFL = Program/Tests
CABAL_PREFIX=cabal exec --
PATTERN=
GHC_FLAGS=-rtsopts -O2 $(GHC_ASSERT)

# all.test giffhorn.test cdom.test balanced.test timing.test soundness.test all should be .PHONY targets here, but the pattern rules below dont like that
.PHONY: all  rofl .FORCE

all : all.test all.fail rofl

%.test.bin : .FORCE
	$(CABAL_PREFIX) ghc              $(THREADED) $(GHC_FLAGS) --make $(VALID) -main-is $(VALID).$(patsubst %.test.bin,%,$@) -o $@
ifdef PROF
	$(CABAL_PREFIX) ghc $(PROF_GHC)  $(THREADED) $(GHC_FLAGS) --make $(VALID) -main-is $(VALID).$(patsubst %.test.bin,%,$@) -o $@
endif
ifdef DEBUG
	$(CABAL_PREFIX) ghc $(DEBUG_GHC) $(THREADED) $(GHC_FLAGS) --make $(VALID) -main-is $(VALID).$(patsubst %.test.bin,%,$@) -o $@
endif

%.fail.bin : .FORCE
	$(CABAL_PREFIX) ghc              $(THREADED) $(GHC_FLAGS) --make $(INVALID) -main-is $(INVALID).$(patsubst %.fail.bin,%,$@) -o $@
ifdef PROF
	$(CABAL_PREFIX) ghc $(PROF_GHC)  $(THREADED) $(GHC_FLAGS) --make $(INVALID) -main-is $(INVALID).$(patsubst %.fail.bin,%,$@) -o $@
endif
ifdef DEBUG
	$(CABAL_PREFIX) ghc $(DEBUG_GHC) $(THREADED) $(GHC_FLAGS) --make $(INVALID) -main-is $(INVALID).$(patsubst %.fail.bin,%,$@) -o $@
endif


%.test-xml.bin : .FORCE
	$(CABAL_PREFIX) ghc              $(THREADED) $(GHC_FLAGS) --make $(VALID) -main-is $(VALID).$(patsubst %.test-xml.bin,%,$@)X -o $@
ifdef PROF
	$(CABAL_PREFIX) ghc $(PROF_GHC)  $(THREADED) $(GHC_FLAGS) --make $(VALID) -main-is $(VALID).$(patsubst %.test-xml.bin,%,$@)X -o $@
endif
ifdef DEBUG
	$(CABAL_PREFIX) ghc $(DEBUG_GHC) $(THREADED) $(GHC_FLAGS) --make $(VALID) -main-is $(VALID).$(patsubst %.test-xml.bin,%,$@)X -o $@
endif

%.fail-xml.bin : .FORCE
	$(CABAL_PREFIX) ghc              $(THREADED) $(GHC_FLAGS) --make $(INVALID) -main-is $(INVALID).$(patsubst %.fail-xml.bin,%,$@)X -o $@
ifdef PROF
	$(CABAL_PREFIX) ghc $(PROF_GHC)  $(THREADED) $(GHC_FLAGS) --make $(INVALID) -main-is $(INVALID).$(patsubst %.fail-xml.bin,%,$@)X -o $@
endif
ifdef DEBUG
	$(CABAL_PREFIX) ghc $(DEBUG_GHC) $(THREADED) $(GHC_FLAGS) --make $(INVALID) -main-is $(INVALID).$(patsubst %.fail-xml.bin,%,$@)X -o $@
endif


%.test : %.test.bin .FORCE
	./$< $(RTS) $(PATTERN) $(COLOR)

%.test.xml : %.test-xml.bin
	touch $@
	./$< $(RTS) $(PATTERN) --xml $@


%.test.xml.fixed.xml : %.test.xml
	cat $< | sed -e 's/<testsuites[^>]*>//g' | sed -e 's/<\/testsuites>//g' > $@

unitTestReports/%.test.xml.fixed.xml/html/index.html : %.test.xml .FORCE
	ant -v -buildfile test-xml-to-html.xml -Dxmlfile=$<.fixed.xml

unitTestReports/%.test.xml/html/index.html : %.test.xml .FORCE
	ant -v -buildfile test-xml-to-html.xml -Dxmlfile=$<

%.fail : %.fail.bin .FORCE
	./$< $(RTS) $(PATTERN) $(COLOR)

%.fail.xml : %.fail-xml.bin
	touch $@
	./$< $(RTS) $(PATTERN) --xml $@


$(ROFL) : .FORCE
	$(CABAL_PREFIX) ghc              $(THREADED) $(GHC_FLAGS) --make Program.Tests -main-is Program.Tests.main -o $@
ifdef PROF
	$(CABAL_PREFIX) ghc $(PROF_GHC)  $(THREADED) $(GHC_FLAGS) --make Program.Tests -main-is Program.Tests.main -o $@
endif
ifdef DEBUG
	$(CABAL_PREFIX) ghc $(DEBUG_GHC) $(THREADED) $(GHC_FLAGS) --make Program.Tests -main-is Program.Tests.main -o $@
endif

rofl : $(ROFL)
	$(ROFL) $(RTS)

clean :
	find -name "*.hi"      -not -path "./.cabal-sandbox/*" -delete
	find -name "*.dyn_hi"  -not -path "./.cabal-sandbox/*" -delete
	find -name "*.o"       -not -path "./.cabal-sandbox/*" -delete
	find -name "*.dyn_o"   -not -path "./.cabal-sandbox/*" -delete
	find -name "*.p_o"     -not -path "./.cabal-sandbox/*" -delete
	find -name "*~"        -not -path "./.cabal-sandbox/*" -delete
