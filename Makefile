THREADED="-threaded"
RTS="+RTS -N -RTS"
ROFL = Data/Graph/Inductive/Query/BalancedSCC


# all.test giffhorn.test cdom.test balanced.test timing.test all should be .PHONY targets here, but the pattern rules below dont like that
.PHONY: all  rofl .FORCE

all : all.test rofl

%.test.bin : .FORCE
	ghc $(THREADED) -O --make Program.Properties.ValidProperties -main-is Program.Properties.ValidProperties.$(patsubst %.test.bin,%,$@) -o $@

%.test : %.test.bin .FORCE
	./$< $(RTS)

$(ROFL) : .FORCE
	ghc $(THREADED) -O --make Data.Graph.Inductive.Query.BalancedSCC -main-is Data.Graph.Inductive.Query.BalancedSCC.rofl

rofl : $(ROFL)
	$(ROFL) $(RTS)
