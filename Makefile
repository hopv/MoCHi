EXE = src/mochi.exe

################################################################################
# main target

.PHONY: main

main: $(EXE)

$(EXE):
	dune build


################################################################################
# distributions

.PHONY: dist bin

dist:
	git archive HEAD -o dist.tar.gz

bin: $(EXE)
	bash scripts/pack_bin.sh


################################################################################
# clean

.PHONY: clean

clean:
	dune clean
