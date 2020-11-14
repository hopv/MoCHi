include Makefile.config

FPAT=fpat
MOCHI_BIN_DIR = mochi_bin
DOC = doc
SRC = src

################################################################################
# main target

.PHONY: main

EXE = mochi.exe

main: $(EXE)
$(EXE):
	$(DUNE) build


################################################################################
# libraries

.PHONY: install-lib csisat fpat

install-lib: fpat csisat
csisat:
	cd csisat && dune build --root . && dune install --root .

fpat: csisat
	cd fpat && autoconf && ./configure && make install-lib all install


################################################################################
# distribution

ifdef GIT
.PHONY: dist

dist:
	$(GIT) archive HEAD -o dist.tar.gz
endif

.PHONY: bin

bin: $(EXE)
	@echo make $(MOCHI_BIN_DIR)
	@mkdir -p $(MOCHI_BIN_DIR)/bin
	@touch no
	@cp $(CVC3) $(HORSAT) $(HORSAT2) $(TRECS) $(HORSATP) $(HOICE) $(Z3_BIN) $(SRC)/$(EXE) $(MOCHI_BIN_DIR)/bin
	@rm no
	@mkdir -p $(MOCHI_BIN_DIR)/lib
	@ldd $(MOCHI_BIN_DIR)/bin/$(EXE) | while read line; \
	do \
	   if [ $$(echo $$line | wc -w) -eq 2 ]; then \
	     cp $$(echo $$line | cut -d' ' -f1) $(MOCHI_BIN_DIR)/lib ; \
	   elif [ $$(echo $$line | wc -w) -eq 4 ]; then \
	     cp $$(echo $$line | cut -d' ' -f3) $(MOCHI_BIN_DIR)/lib ; \
	   fi; \
	done
	@mkdir -p $(MOCHI_BIN_DIR)/stdlib
	@cp $$($(OCAMLFIND) ocamlc -where)/*.cmi $(MOCHI_BIN_DIR)/stdlib
	@tar czvf $(MOCHI_BIN_DIR).tar.gz $(MOCHI_BIN_DIR)


################################################################################
# documents

.PHONY: doc

doc:
	mkdir -p $(DOC)
	$(OCAMLFIND) ocamldoc -html -d $(DOC) $(MLI)
	perl -pi -e 's/charset=iso-8859-1/charset=utf8/' $(DOC)/*.html


################################################################################
# clean

.PHONY: clean clean-all

clean:
	$(DUNE) clean

clean-all: clean
	cd $(FPAT) && make clean && cd atp && make clean
	cd csisat && dune clean --root .
