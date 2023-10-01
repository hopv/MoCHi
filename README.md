[![Docker Image CI](https://github.com/hopv/MoCHi/actions/workflows/docker-image.yml/badge.svg)](https://github.com/hopv/MoCHi/actions/workflows/docker-image.yml)

MoCHi is a software model checker for OCaml.
MoCHi is based on higher-order model checking, predicate abstraction, and CEGAR.


How to build MoCHi
==================

 Install the required tools/libraries listed below,
 and run "bash build", which generates "src/mochi.exe".


What do you need?
=================

- OCaml >=4.08.0 & <5.0.0
- opam >=2.1
- Git
- Autoconf
- Tools/Libraries available via opam
  (Run "opam install . --deps-only -y")
    - Z3 >=4.8.9
    - dune >=2.5.1
    - batteries >=3.4.0
    - ocamlfind/findlib
    - ppx_deriving
    - Yojson
    - camlp5
    - Menhir
    - smtlib-utils >=0.3.1
    - csisat
    - Fpat
    - atp
- HorSat2 binary (https://github.com/hopv/horsat2)


Licenses
========

 This software is licensed under the Apache License, Version 2.0 (http://www.apache.org/licenses/LICENSE-2.0.txt).


Author
======

 MoCHi is developed/maintained by Ryosuke SATO <rsato@is.s.u-tokyo.ac.jp>


Contributors
============

- Naoki Kobayashi
- Hiroshi Unno
- Takuya Kuwahara
- Keiichi Watanabe
- Naoki Iwayama
