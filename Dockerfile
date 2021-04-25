FROM ubuntu:20.04

ARG ocaml_ver=4.09.1

RUN apt-get update && \
    apt-get install -y git make gcc m4 opam libgmp-dev libmpfr-dev libglpk-dev autoconf libipc-system-simple-perl libstring-shellquote-perl

RUN useradd -m mochi
USER mochi
WORKDIR /home/mochi

RUN opam init -y --comp=$ocaml_ver --disable-sandboxing && \
    eval `opam config env` && \
    opam install -y z3 camlp5 ocamlfind zarith apron batteries yojson ppx_deriving dune menhir

COPY --chown=mochi:mochi . .

ENV OCAMLFIND_IGNORE_DUPS_IN /home/mochi/.opam/$ocaml_ver/lib/ocaml/compiler-libs

RUN eval $(opam env) && \
    autoconf && \
    touch trecs && chmod +x trecs && \
    ./configure && \
    make install-lib && \
    make && \
    LD_LIBRARY_PATH=/home/mochi/.opam/$ocaml_ver/lib/z3 ./src/mochi.exe -v
