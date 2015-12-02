TEST = Program/Properties/ValidProperties


.PHONY: test .FORCE

$(TEST) : .FORCE
	ghc -threaded -O --make Program.Properties.ValidProperties -main-is Program.Properties.ValidProperties
test : $(TEST)
	$(TEST) +RTS -N -RTS
