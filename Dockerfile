FROM ubuntu:16.04

ARG ocaml_var=4.03.0

RUN apt-get update && \
    apt-get install -y git make gcc m4 opam libgmp-dev libmpfr-dev libglpk-dev autoconf

RUN useradd -m mochi
USER mochi
WORKDIR /home/mochi

RUN opam init -y --comp=$ocaml_var && \
    eval `opam config env` && \
    opam install -y camlp4 camlp5 ocamlfind zarith apron batteries yojson ppx_deriving z3

COPY . .

ENV OCAMLFIND_IGNORE_DUPS_IN /home/mochi/.opam/4.03.0/lib/ocaml/compiler-libs

RUN eval `opam config env` && \
    autoconf && \
    touch trecs && chmod +x trecs && \
    ./configure && \
    make install-lib && \
    make -B depend && \
    make opt && \
    LD_LIBRARY_PATH=/home/mochi/.opam/$ocaml_var/lib/z3 ./mochi.opt -v
