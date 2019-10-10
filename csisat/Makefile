RM = rm -rf
PWD = $(shell pwd)

OBJ = obj
SRC = src
DOC = doc
BIN = bin
LIB =/usr/lib #lib

INCLUDE=/usr/include
LIBS=-ccopt -L$(LIB) -cclib -lglpk -cclib -L$(LIB_DIR) -cclib -lcsisat

OCAML_C = $(shell if which ocamlc.opt 2> /dev/null > /dev/null ; then echo ocamlc.opt; else echo ocamlc; fi)
OCAML_LD = $(OCAML_C)
OCAML_OPT_C = $(shell if which ocamlopt.opt 2> /dev/null > /dev/null ; then echo ocamlopt.opt; else echo ocamlopt; fi)
OCAML_OPT_LD = $(OCAML_OPT_C)
OCAML_OPT_LEX = $(shell if which ocamllex.opt 2> /dev/null > /dev/null ; then echo ocamllex.opt; else echo ocamllex; fi)
OCAML_OPT_YACC = $(shell if which ocamlyacc.opt 2> /dev/null > /dev/null ; then echo ocamlyacc.opt; else echo ocamlyacc; fi)

COMPILE_FLAG = #-inline 10
#COMPILE_FLAG = -inline 10 -unsafe -noassert
#COMPILE_FLAG = -p
OCAML_LD_FLAGS =

DIRS = $(OBJ) $(BIN)

FILES = \
	$(OBJ)/camlglpk.cmx \
	$(OBJ)/csisatGlobal.cmx \
	$(OBJ)/csisatMessage.cmx \
	$(OBJ)/csisatOrdSet.cmx \
	$(OBJ)/csisatUtils.cmx \
	$(OBJ)/csisatAst.cmx \
	$(OBJ)/csisatAstUtil.cmx \
	$(OBJ)/csisatLIUtils.cmx \
	$(OBJ)/csisatDpllClause.cmx \
	$(OBJ)/csisatDpllProof.cmx \
	$(OBJ)/csisatSatInterface.cmx \
	$(OBJ)/csisatDpllCore.cmx \
	$(OBJ)/csisatMatrix.cmx \
	$(OBJ)/csisatInfixLex.cmx \
	$(OBJ)/csisatInfixParse.cmx \
	$(OBJ)/csisatFociPrinter.cmx \
	$(OBJ)/csisatFociLex.cmx \
	$(OBJ)/csisatFociParse.cmx \
	$(OBJ)/csisatDimacsLex.cmx \
	$(OBJ)/csisatDimacsParse.cmx \
	$(OBJ)/csisatClpLI.cmx \
	$(OBJ)/csisatDag.cmx \
	$(OBJ)/csisatSatUIF.cmx \
	$(OBJ)/csisatSatLI.cmx \
	$(OBJ)/csisatNelsonOppen.cmx \
	$(OBJ)/csisatSatPL.cmx \
	$(OBJ)/csisatInterpolate.cmx \
	$(OBJ)/csisatConfig.cmx \
	$(OBJ)/csisatTests.cmx \
    $(OBJ)/csisatMain.cmx

TARGET = $(BIN)/csisat


all: $(DIRS) lib $(FILES)
	$(OCAML_OPT_C) $(COMPILE_FLAG) -o $(TARGET) $(FILES) $(LIBS) $(CAMLGLPK)
	$(shell sed -i 's/Version .*\\n\\n/Version 1.2 (Rev REV, Build DATE)\.\\n\\n/g' $(SRC)/csisatConfig.ml)

$(OBJ):
	mkdir -p $(OBJ)

$(BIN):
	mkdir -p $(BIN)

VERSION = $(shell svnversion)
DATE = $(shell date -u +%Y-%m-%dT%H:%M:%S)

### Part for parsers and lexers ####

#FOCI-like syntax
$(OBJ)/csisatFociParse.mli: $(OBJ)/csisatFociParse.ml

$(OBJ)/csisatFociParse.cmi: $(OBJ)/csisatFociParse.mli
	$(OCAML_OPT_C) $(COMPILE_FLAG) -I $(OBJ) $(INLCUDES) -c $<
	$(OCAML_C) -I $(OBJ) $(INLCUDES) -c $<

$(OBJ)/csisatFociLex.cmx: $(OBJ)/csisatFociParse.cmi $(OBJ)/csisatFociLex.ml
	$(OCAML_OPT_C) $(COMPILE_FLAG) -I $(OBJ) $(INLCUDES) -c $(OBJ)/csisatFociLex.ml
	$(OCAML_C) -I $(OBJ) $(INLCUDES) -c $(OBJ)/csisatFociLex.ml

#INFIX syntax
$(OBJ)/csisatInfixParse.mli: $(OBJ)/csisatInfixParse.ml

$(OBJ)/csisatInfixParse.cmi: $(OBJ)/csisatInfixParse.mli
	$(OCAML_OPT_C) $(COMPILE_FLAG) -I $(OBJ) $(INLCUDES) -c $<
	$(OCAML_C) -I $(OBJ) $(INLCUDES) -c $<

$(OBJ)/csisatInfixLex.cmx: $(OBJ)/csisatInfixParse.cmi $(OBJ)/csisatInfixLex.ml
	$(OCAML_OPT_C) $(COMPILE_FLAG) -I $(OBJ) $(INLCUDES) -c $(OBJ)/csisatInfixLex.ml
	$(OCAML_C) -I $(OBJ) $(INLCUDES) -c $(OBJ)/csisatInfixLex.ml

#DIMACS syntax
$(OBJ)/csisatDimacsParse.mli: $(OBJ)/csisatDimacsParse.ml

$(OBJ)/csisatDimacsParse.cmi: $(OBJ)/csisatDimacsParse.mli
	$(OCAML_OPT_C) $(COMPILE_FLAG) -I $(OBJ) $(INLCUDES) -c $<
	$(OCAML_C) -I $(OBJ) $(INLCUDES) -c $<

$(OBJ)/csisatDimacsLex.cmx: $(OBJ)/csisatDimacsParse.cmi $(OBJ)/csisatDimacsLex.ml
	$(OCAML_OPT_C) $(COMPILE_FLAG) -I $(OBJ) $(INLCUDES) -c $(OBJ)/csisatDimacsLex.ml
	$(OCAML_C) -I $(OBJ) $(INLCUDES) -c $(OBJ)/csisatDimacsLex.ml

####################################

$(OBJ)/%.ml: $(SRC)/io/%.mll
	@mkdir -p $(OBJ)
	$(OCAML_OPT_LEX) -o $@ $<

$(OBJ)/%.ml: $(SRC)/io/%.mly
	@mkdir -p $(OBJ)
	$(OCAML_OPT_YACC) $<
	@mv $(patsubst %.mly, %.ml, $<) $@
	@mv $(patsubst %.mly, %.mli, $<) $(patsubst %.ml, %.mli, $@)


$(OBJ)/%.cmx: $(OBJ)/%.ml
	$(OCAML_OPT_C) $(COMPILE_FLAG) -I $(OBJ) $(INLCUDES) -c $<
	$(OCAML_C) -I $(OBJ) $(INLCUDES) -c $<

$(OBJ)/%.cmx: $(SRC)/%.ml
	@mkdir -p $(OBJ)
	$(shell if test $< = $(SRC)/csisatConfig.ml; \
		then sed -i 's/Rev REV, Build DATE/Rev $(VERSION), Build $(DATE)/g' $<; fi)
	$(OCAML_OPT_C) $(COMPILE_FLAG) -I $(OBJ) $(INLCUDES) -c $<
	@mv $(patsubst %.ml, %.cmx, $<) $@
	@mv $(patsubst %.ml, %.cmi, $<) $(patsubst %.cmx, %.cmi, $@)
	@mv $(patsubst %.ml, %.o, $<) $(patsubst %.cmx, %.o, $@)

$(OBJ)/%.o: $(SRC)/%.c
	$(OCAML_C) -c -ccopt -I$(INCLUDE) -ccopt -o -ccopt $@ $<

LIB_DIR = lib
OCAML_LIB = libcsisat

lib: $(LIB_DIR)/$(OCAML_LIB).cmxa

GLPK_OBJ = $(SRC)/camlglpk_stubs.o

$(LIB_DIR)/$(OCAML_LIB).cmxa $(LIB_DIR)/$(OCAML_LIB).a: $(GLPK_LIB) $(FILES) $(GLPK_OBJ)
	@echo Creating OCAML \(native code\) library $@
	@mkdir -p $(LIB_DIR)
	$(OCAML_OPT_LD) $(OCAML_LD_FLAGS) -a -o $@ $(FILES)
	ar q $(LIB_DIR)/$(OCAML_LIB).a $(GLPK_OBJ)

.PHONY: doc lib

doc: odoc

HIDE = Set.Make,Char

odoc:
	$(shell if test -e $(DOC)/index.html ; then rm -rf $(DOC)/* ; fi)
	@mkdir -p $(DOC)
	ocamldoc \
		-v \
		-d $(DOC) \
		-I $(OBJ) $(INLCUDES) \
		-html \
		-stars \
		-hide $(HIDE) \
		$(patsubst $(OBJ)/%, $(SRC)/%, $(patsubst %.cmx, %.ml, $(FILES)))

clean:
	$(RM) $(TARGET) $(OBJ)/*
