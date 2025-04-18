MoCHi is a software model checker for OCaml.
MoCHi is based on higher-order model checking, predicate abstraction, and CEGAR.


How to install
==============

 Run `opam pin add mochi git@github.com:hopv/MoCHi.git`.


How to build
============

 Install the required tools/libraries listed below,
 and run "dune build", which generates "src/mochi.exe".


What do you need?
=================

- OCaml >=4.08.0 & <5.2.0
    - OCaml 4.13 and 4.14 are recommended
- opam >=2.1
- Git
- Tools/Libraries available via opam
  (Run "opam install . --deps-only -y")
    - Z3 >=4.8.9
    - dune >=2.8
    - batteries >=3.4.0
    - ocamlfind/findlib
    - ppx_deriving
    - ppxlib
    - Yojson
    - Menhir
    - Fpat
    - csisat
    - atp
    - smtlib-utils >=0.3.1
    - ocamlgraph
    - dune-build-info
    - bos
- HorSat2 binary (https://github.com/hopv/horsat2)
- HoIce binary (https://github.com/hopv/hoice)
    - HoIce is not required to run MoCHi, but the lack of HoIce may degrade the performance. (See [[Sato+ PEPM2019]](https://doi.org/10.1145/3294032.3294081))


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
- Hiroyuki Katsura
