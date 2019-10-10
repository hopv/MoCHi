# List of ML files to compile as a library. This leaves out the following
# which are probably not much use:
#
# sigma.ml       (Sigma-formulas and evaluator-by-proof)
# turing.ml      (OCaml implementation of Turing machines)
# undecidable.ml (Proofs related to undecidability results)
# bhk.ml         (Trivial instance of BHK interpretation)
# many.ml        (Example relevant to many-sorted logic)
# hol.ml         (Simple higher order logic setup)

# Use camlp5 for versions of OCaml >= 3.10
# Download this from http://pauillac.inria.fr/~ddr/camlp5/

USE_CAMLP5=true

MLFILES = initialization.ml lib.ml intro.ml formulas.ml prop.ml propexamples.ml           \
          defcnf.ml dp.ml stal.ml bdd.ml fol.ml skolem.ml               \
          herbrand.ml unif.ml tableaux.ml resolution.ml prolog.ml       \
          meson.ml skolems.ml equal.ml cong.ml rewrite.ml               \
          order.ml completion.ml eqelim.ml                              \
          paramodulation.ml decidable.ml qelim.ml cooper.ml             \
          complex.ml real.ml grobner.ml geom.ml interpolation.ml        \
          combining.ml lcf.ml lcfprop.ml folderived.ml lcffol.ml        \
          tactics.ml #limitations.ml

all: atp_batch.cmxa atp_batch.cma

atp_batch.cmxa: atp_batch.cmx
	ocamlopt -a -o $@ $^

atp_batch.cma: atp_batch.cmo
	ocamlc -a -o $@ $^

# The default is an interactive session skipping the examples.

interactive: atp_interactive.ml init.ml; echo '#use "init.ml";;' >.ocamlinit; (sleep 3s; rm -f .ocamlinit) & ocaml

# Build a bytecode executable

bytecode: example.ml atp_batch.cmo;                                                                             \
                if ${USE_CAMLP5};                                                                               \
                then ocamlc -pp "camlp5o ./Quotexpander.cmo" -o example nums.cma atp_batch.cmo example.ml;      \
                else ocamlc -pp "camlp4o ./Quotexpander.cmo" -o example nums.cma atp_batch.cmo example.ml;      \
                fi

# Alternatively, produce native code

compiled: example.ml atp_batch.cmx;                                                                             \
                if ${USE_CAMLP5};                                                                               \
                then ocamlopt -pp "camlp5o ./Quotexpander.cmo" -o example nums.cmxa atp_batch.cmx example.ml;   \
                else ocamlopt -pp "camlp4o ./Quotexpander.cmo" -o example nums.cmxa atp_batch.cmx example.ml;   \
                fi

# Make the appropriate object for the main body of code

atp_batch.cmx: Quotexpander.cmo atp_batch.ml;                                                                   \
                if ${USE_CAMLP5};                                                                               \
                then ocamlopt -pp "camlp5o ./Quotexpander.cmo" -w ax -c atp_batch.ml;                           \
                else ocamlopt -pp "camlp4o ./Quotexpander.cmo" -w ax -c atp_batch.ml;                           \
                fi

atp_batch.cmo: Quotexpander.cmo atp_batch.ml;                                                                   \
                if ${USE_CAMLP5};                                                                               \
                then ocamlc -pp "camlp5o ./Quotexpander.cmo" -w ax -c atp_batch.ml;                             \
                else ocamlc -pp "camlp4o ./Quotexpander.cmo" -w ax -c atp_batch.ml;                             \
                fi

# Make the camlp4 or camlp5 quotation expander

Quotexpander.cmo: Quotexpander.ml; if ${USE_CAMLP5};                                                            \
                                    then ocamlfind ocamlc -package camlp5 -c Quotexpander.ml;                                  \
                                    else ocamlfind ocamlc -package camlp4 -c Quotexpander.ml;                                  \
                                    fi

# Extract the non-interactive part of the code

atp_interactive.ml: $(MLFILES); ./Mk_ml_file $(MLFILES) >atp_interactive.ml

atp_batch.ml: $(MLFILES); ./Mk_ml_file $(MLFILES) | grep -v install_printer >atp_batch.ml

# Clean up

clean:; -rm -f atp_batch.cma atp_batch.cmi atp_batch.cmo atp_batch.cmx atp_batch.o atp_batch.ml example example.exe example.cmi example.cmo example.cmx example.o Quotexpander.cmo Quotexpander.cmi atp_interactive.ml .ocamlinit
