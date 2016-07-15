TEST = Program/Properties/ValidProperties
ROFL = Data/Graph/Inductive/Query/BalancedSCC


.PHONY: test rofl .FORCE

$(TEST) : .FORCE
	ghc -threaded -O --make Program.Properties.ValidProperties -main-is Program.Properties.ValidProperties
test : $(TEST)
	$(TEST) +RTS -N -RTS

$(ROFL) : .FORCE
	ghc -O --make Data.Graph.Inductive.Query.BalancedSCC -main-is Data.Graph.Inductive.Query.BalancedSCC.rofl

rofl : $(ROFL)
	$(ROFL)
