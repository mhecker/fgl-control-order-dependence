# uncomment for profiling builds
PROF=defined

ifdef PROF
PROF_GHC=-prof -fprof-auto -osuf p_o
PROF_RTS=-p
endif

THREADED=-threaded
RTS=+RTS -N $(PROF_RTS) -RTS
COLOR=--color always
ROFL = Program/Tests
CABAL_PREFIX=cabal exec --
PATTERN=
GHC_FLAGS=-rtsopts -O -fno-ignore-asserts

# all.test giffhorn.test cdom.test balanced.test timing.test soundness.test all should be .PHONY targets here, but the pattern rules below dont like that
.PHONY: all  rofl .FORCE

all : all.test all.fail rofl

%.test.bin : .FORCE
	$(CABAL_PREFIX) ghc             $(THREADED) $(GHC_FLAGS) --make Program.Properties.ValidProperties -main-is Program.Properties.ValidProperties.$(patsubst %.test.bin,%,$@) -o $@
ifdef PROF
	$(CABAL_PREFIX) ghc $(PROF_GHC) $(THREADED) $(GHC_FLAGS) --make Program.Properties.ValidProperties -main-is Program.Properties.ValidProperties.$(patsubst %.test.bin,%,$@) -o $@
endif

%.fail.bin : .FORCE
	$(CABAL_PREFIX) ghc             $(THREADED) $(GHC_FLAGS) --make Program.Properties.InvalidProperties -main-is Program.Properties.InvalidProperties.$(patsubst %.fail.bin,%,$@) -o $@
ifdef PROF
	$(CABAL_PREFIX) ghc $(PROF_GHC) $(THREADED) $(GHC_FLAGS) --make Program.Properties.InvalidProperties -main-is Program.Properties.InvalidProperties.$(patsubst %.fail.bin,%,$@) -o $@
endif


%.test-xml.bin : .FORCE
	$(CABAL_PREFIX) ghc             $(THREADED) $(GHC_FLAGS) --make Program.Properties.ValidProperties -main-is Program.Properties.ValidProperties.$(patsubst %.test-xml.bin,%,$@)X -o $@
ifdef PROF
	$(CABAL_PREFIX) ghc $(PROF_GHC) $(THREADED) $(GHC_FLAGS) --make Program.Properties.ValidProperties -main-is Program.Properties.ValidProperties.$(patsubst %.test-xml.bin,%,$@)X -o $@
endif

%.fail-xml.bin : .FORCE
	$(CABAL_PREFIX) ghc             $(THREADED) $(GHC_FLAGS) --make Program.Properties.InvalidProperties -main-is Program.Properties.InvalidProperties.$(patsubst %.fail-xml.bin,%,$@)X -o $@
ifdef PROF
	$(CABAL_PREFIX) ghc $(PROF_GHC) $(THREADED) $(GHC_FLAGS) --make Program.Properties.InvalidProperties -main-is Program.Properties.InvalidProperties.$(patsubst %.fail-xml.bin,%,$@)X -o $@
endif


%.test : %.test.bin .FORCE
	./$< $(RTS) $(PATTERN) $(COLOR)

%.test.xml : %.test-xml.bin
	./$< $(RTS) $(PATTERN) --xml $@


%.fail : %.fail.bin .FORCE
	./$< $(RTS) $(PATTERN) $(COLOR)

%.fail.xml : %.fail-xml.bin
	./$< $(RTS) $(PATTERN) --xml $@


$(ROFL) : .FORCE
	$(CABAL_PREFIX) ghc             $(THREADED) $(GHC_FLAGS) --make Program.Tests -main-is Program.Tests.main -o $@
ifdef PROF
	$(CABAL_PREFIX) ghc $(PROF_GHC) $(THREADED) $(GHC_FLAGS) --make Program.Tests -main-is Program.Tests.main -o $@
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
