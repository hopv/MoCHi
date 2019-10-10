include Makefile.config

.PHONY: main all byte opt top clean doc test

PACKAGES = fpat,str,unix,batteries,compiler-libs.common,z3,yojson,ppx_deriving.show

FPAT=fpat
MOCHI_BIN_DIR = mochi_bin

WARN_FLAGS = -w -52-57-58
OCAMLCFLAGS = -g -annot -bin-annot $(WARN_FLAGS) -package $(PACKAGES)
OCAMLOPTFLAGS = -g -annot -bin-annot $(WARN_FLAGS) -package $(PACKAGES)

DOC = doc

################################################################################
# main target

NAME = mochi

main: opt
all: depend byte opt top

byte: $(NAME).byte
opt: $(NAME).opt
top: $(NAME).top


ifdef GIT
GIT_FILES = $(shell git ls-files)
endif

ifdef GIT
revision.ml: .git/logs/HEAD $(GIT_FILES)
endif

main: revision.ml
revision.ml: $(FPAT_LIB) Makefile Makefile.config
	@echo make revision.ml
	@rm -f $@
ifdef GIT
	@echo -n 'let mochi = Some ("' >> $@
	@if [ $$(${GIT} diff | wc -w) != 0 ]; then echo -n _ >> $@; fi
	@echo -n `$(GIT) rev-parse --short HEAD` >> $@
	@echo -n '", "' >> $@
	@if [ $$(${GIT} diff | wc -w) != 0 ]; then echo -n "after " >> $@; fi
	@$(GIT) log --date=iso --pretty=format:"%ad" -1 >> $@
	@echo '")' >> $@
else
	@echo "let mochi = None" >> $@
endif



################################################################################
# libraries

.PHONY: csisat fpat

install-lib: fpat
csisat:
	cd csisat && make lib

fpat: csisat
	cd fpat && autoconf && ./configure && make install-lib all install

################################################################################
# bytecode and native-code compilation

MLI = lift.mli CPS.mli curry.mli encode_rec.mli encode_list.mli		\
	feasibility.mli refine.mli syntax.mli print.mli term_util.mli	\
	CEGAR_print.mli CEGAR_CPS.mli CEGAR_abst.mli spec_parser.mli	\
	horSat_parser.mli trecs_parser.mli CEGAR_parser.mli		\
	BRA_transform.mli CEGAR_lift.mli tupling.mli ref_trans.mli	\
	trans.mli tree.mli rose_tree.mli type.mli color.mli		\
	CEGAR_trans.mli CEGAR_util.mli fair_termination_type.mli	\
	HORS_parser.mli fpatInterface.mli ref_type.mli encode.mli	\
	ref_type_gen.mli modular_common.mli CEGAR_abst_CPS.mli		\
	CEGAR_abst_util.mli ref_type_check.mli				\
	ref_type_pred_typing.mli slice.mli graph.mli
CMI = $(MLI:.mli=.cmi)

CMO = revision.cmo mconfig.cmo util.cmo flag.cmo debug.cmo graph.cmo	\
	mochi_util.cmo menv.cmo color.cmo tree.cmo rose_tree.cmo	\
	sexp.cmo id.cmo type.cmo syntax.cmo print.cmo term_util.cmo	\
	CEGAR_type.cmo CEGAR_syntax.cmo CEGAR_print.cmo			\
	CEGAR_util.cmo typing.cmo type_check.cmo CEGAR_ref_type.cmo	\
	smtlib2_interface.cmo fpatInterface.cmo QE.cmo			\
	rec_CHC_solver.cmo ref_type.cmo eval.cmo quick_check.cmo	\
	spec.cmo problem.cmo ref_type_gen.cmo trans.cmo effect.cmo	\
	slice.cmo trans_problem.cmo CHC.cmo ref_type_check.cmo		\
	CFA.cmo uncurry.cmo lift.cmo fair_termination_util.cmo		\
	CEGAR_lift.cmo useless_elim.cmo inter_type.cmo type_trans.cmo	\
	CPS.cmo curry.cmo CEGAR_CPS.cmo parser_wrapper.cmo		\
	encode_list.cmo encode_rec.cmo encode_rec_variant.cmo		\
	encode.cmo omegaInterface.cmo CEGAR_abst_util.cmo		\
	CEGAR_trans.cmo CEGAR_abst_CPS.cmo CEGAR_abst.cmo		\
	CEGAR_parser.cmo CEGAR_lexer.cmo spec_parser.cmo		\
	spec_lexer.cmo trecs_syntax.cmo trecs_parser.cmo		\
	trecs_lexer.cmo trecsInterface.cmo horSat_syntax.cmo		\
	horSat_parser.cmo horSat_lexer.cmo horSatInterface.cmo		\
	horSat2_parser.cmo horSat2_lexer.cmo horSat2Interface.cmo	\
	feasibility.cmo refine.cmo CEGAR_non_term.cmo HORS_syntax.cmo	\
	HORS_lexer.cmo HORS_parser.cmo horSatPInterface.cmo		\
	CEGAR_fair_non_term.cmo ModelCheck.cmo CEGAR.cmo		\
	writeAnnot.cmo tupling.cmo ref_trans.cmo ret_fun.cmo		\
	BRA_types.cmo BRA_util.cmo BRA_state.cmo BRA_transform.cmo	\
	extraClsDepth.cmo extraParamInfer.cmo elim_same_arg.cmo		\
	ref_type_pred_typing.cmo preprocess.cmo main_loop.cmo		\
	modular_common.cmo comp_tree.cmo horn_clause.cmo		\
	modular_infer.cmo modular_check.cmo modular.cmo			\
	termination_loop.cmo fair_termination.cmo verify_ref_typ.cmo	\
	verify_module.cmo cmd.cmo mochi.cmo

CMX = $(CMO:.cmo=.cmx)
CMA =
CMXA = $(CMA:.cma=.cmxa)

PARSER_LEXER = spec horSat horSat2 trecs CEGAR HORS
GENERATED = $(addsuffix _parser.ml,$(PARSER_LEXER)) \
	$(addsuffix _parser.mli,$(PARSER_LEXER)) \
	$(addsuffix _lexer.ml,$(PARSER_LEXER)) \
	parser_wrapper.ml


$(NAME).byte: $(CMO)
	$(OCAMLFIND) ocamlc $(OCAMLCFLAGS) -linkpkg -o $@ $(CMA) $(CMO)

$(NAME).opt: $(CMX)
	$(OCAMLFIND) ocamlopt $(OCAMLOPTFLAGS) -linkpkg -o $@ $(CMXA) $(CMX)

$(NAME).top: $(CMO)
	$(OCAMLFIND) ocamlmktop $(OCAMLCFLAGS) -linkpkg -o $@ $(CMA) $(CMO)


parser_wrapper.ml: parser_wrapper_$(OCAML_MAJOR_VER).ml
	cp -f $< $@
	@chmod -w $@


# Dependencies
DEP_FPAT = CEGAR CEGAR_syntax CEGAR_abst_util feasibility mochi \
	main_loop termination_loop refine syntax trans fpatInterface writeAnnot BRA_types term_util
FPAT_LIB = $(FPAT)/fpat.cmi $(FPAT)/fpat.cma $(FPAT)/fpat.cmxa
$(addsuffix .cmi,$(DEP_FPAT)): $(FPAT_LIB)
$(addsuffix .cmo,$(DEP_FPAT)): $(FPAT_LIB)
$(addsuffix .cmx,$(DEP_FPAT)): $(FPAT_LIB)


# Common rules
.SUFFIXES: .ml .mli .cmo .cmi .cmx .mly .mll

.ml.cmo:
	$(OCAMLFIND) ocamlc $(OCAMLCFLAGS) -c $<

.mli.cmi:
	$(OCAMLFIND) ocamlc $(OCAMLCFLAGS) -c $<

.ml.cmx:
	$(OCAMLFIND) ocamlopt $(OCAMLOPTFLAGS) -c $<

.mly.ml:
	$(OCAMLYACC) -v $<

.mly.mli:
	$(OCAMLYACC) -v $<

.mll.ml:
	$(OCAMLLEX) $<


################################################################################
# distribution

ifdef GIT
.PHONY: dist

dist:
	$(GIT) archive HEAD -o dist.tar.gz
endif

bin: $(NAME).opt
	@echo make $(MOCHI_BIN_DIR)
	@mkdir -p $(MOCHI_BIN_DIR)/bin
	@cp $(CVC3) $(HORSAT) $(HORSAT2) $(TRECS) $(HORSATP) $(HOICE) $(Z3_BIN) $(NAME).opt $(MOCHI_BIN_DIR)/bin
	@mkdir -p $(MOCHI_BIN_DIR)/lib
	@ldd $(NAME).opt | while read line; \
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

doc:
	mkdir -p $(DOC)
	$(OCAMLFIND) ocamldoc -html -d $(DOC) $(MLI)
	perl -pi -e 's/charset=iso-8859-1/charset=utf8/' $(DOC)/*.html


################################################################################
# clean

clean:
	rm -f *.cm[ioxt] *.cmti *.o *.a *.annot *.output *~
	rm -f $(GENERATED)
	rm -f $(NAME).byte $(NAME).opt $(NAME).top
	rm -rf $(MOCHI_BIN_DIR)/bin $(MOCHI_BIN_DIR)/lib $(MOCHI_BIN_DIR)/stdlib

clean-test:
	rm -f */*.trecs_out */*.horsat_out */*.hors */*.annot */*.dot */*.pml

clean-all: clean clean-test
	cd fpat && make clean && cd atp && make clean
	cd csisat && make clean


################################################################################
# test

TEST = sum mult max mc91 ack a-copy-print hors exc-simple exc-fact lock file sum_intro copy_intro fact_notpos fold_right forall_eq_pair forall_leq isnil iter length mem nth nth0 harmonic fold_left zip map_filter risers search fold_fun_list fact_notpos-e harmonic-e map_filter-e search-e
LIMIT = 120
OPTION = -only-result -limit $(LIMIT)

test: opt
	for i in $(TEST); \
	do \
	  echo $$i; \
	  (ulimit -t $(LIMIT); ./mochi.opt test/$$i.ml $(OPTION) 2> /dev/null || echo VERIFICATION FAILED!!!); \
	  echo; \
	done

test-web: opt
	@echo -n "OPTION: "
	@head -1 option.conf
	@echo
	@for i in web/src/*ml; \
	do \
	  echo VERIFY $$i; \
	  ./mochi.opt $$i $(OPTION) 2> /dev/null; \
	  echo; \
	done


test-all: opt
	for i in test/*.ml; \
	do \
	  echo VERIFY $$i; \
	  ./mochi.opt $$i $(OPTION) 2> /dev/null; \
	  echo; \
	done

test-error: opt
	for i in $(TEST); \
	do \
	  echo $$i; \
	  (ulimit -t $(LIMIT); ./mochi.opt test_pepm/$$i.ml $(OPTION) 1> /dev/null); \
	  echo; \
	done

TEST_FT = benchmark/*.ml

test-ft: opt
	for i in hofmann-1.ml hofmann-2.ml koskinen-1.ml koskinen-2.ml koskinen-3-1.ml koskinen-3-2.ml koskinen-3-3.ml koskinen-4.ml lester-1.ml; \
	do \
	  echo $$i; \
	  (ulimit -t $(LIMIT); ./mochi.opt test_fair_termination/$$i -only-result -limit $(LIMIT) 2> /dev/null || echo VERIFICATION FAILED!!!); \
	  echo; \
	done




################################################################################
# depend

SRC = $(CMO:.cmo=.ml)

depend: Makefile $(GENERATED) $(MLI) $(SRC)
	$(OCAMLFIND) ocamldep -package $(PACKAGES) $(MLI) $(SRC) $(GENERATED) > depend

-include depend
