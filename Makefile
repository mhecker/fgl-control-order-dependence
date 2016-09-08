THREADED=-threaded
RTS=+RTS -N -RTS
COLOR=--color always
ROFL = Data/Graph/Inductive/Query/BalancedSCC
CABAL_PREFIX=cabal exec --
PATTERN=

# all.test giffhorn.test cdom.test balanced.test timing.test soundness.test all should be .PHONY targets here, but the pattern rules below dont like that
.PHONY: all  rofl .FORCE

all : all.test all.fail rofl

%.test.bin : .FORCE
	$(CABAL_PREFIX) ghc $(THREADED) -rtsopts -O --make Program.Properties.ValidProperties -main-is Program.Properties.ValidProperties.$(patsubst %.test.bin,%,$@) -o $@

%.fail.bin : .FORCE
	$(CABAL_PREFIX) ghc $(THREADED) -rtsopts -O --make Program.Properties.InvalidProperties -main-is Program.Properties.InvalidProperties.$(patsubst %.fail.bin,%,$@) -o $@


%.test-xml.bin : .FORCE
	$(CABAL_PREFIX) ghc $(THREADED) -rtsopts -O --make Program.Properties.ValidProperties -main-is Program.Properties.ValidProperties.$(patsubst %.test-xml.bin,%,$@)X -o $@

%.fail-xml.bin : .FORCE
	$(CABAL_PREFIX) ghc $(THREADED) -rtsopts -O --make Program.Properties.InvalidProperties -main-is Program.Properties.InvalidProperties.$(patsubst %.fail-xml.bin,%,$@)X -o $@


%.test : %.test.bin .FORCE
	./$< $(RTS) $(PATTERN) $(COLOR)

%.test.xml : %.test-xml.bin
	./$< $(RTS) $(PATTERN) --xml $@


%.fail : %.fail.bin .FORCE
	./$< $(RTS) $(PATTERN) $(COLOR)

%.fail.xml : %.fail-xml.bin
	./$< $(RTS) $(PATTERN) --xml $@


$(ROFL) : .FORCE
	$(CABAL_PREFIX) ghc $(THREADED) -O --make Data.Graph.Inductive.Query.BalancedSCC -main-is Data.Graph.Inductive.Query.BalancedSCC.rofl

rofl : $(ROFL)
	$(ROFL) $(RTS)

clean :
	find -name "*.hi"      -not -path "./.cabal-sandbox/*" -delete
	find -name "*.dyn_hi"  -not -path "./.cabal-sandbox/*" -delete
	find -name "*.o"       -not -path "./.cabal-sandbox/*" -delete
	find -name "*.dyn_o"   -not -path "./.cabal-sandbox/*" -delete
	find -name "*~"        -not -path "./.cabal-sandbox/*" -delete
