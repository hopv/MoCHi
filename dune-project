(lang dune 3.6)
(wrapped_executables false)

(name mochi)

(generate_opam_files true)

(source
 (bitbucket ryosu_sato/mochi))

(authors
 "Ryosuke Sato <rsato@acm.org>"
  "Naoki Kobayashi"
  "Hiroshi Unno"
  "Takuya Kuwahara"
  "Keiichi Watanabe"
  "Naoki Iwayama")

(maintainers "Ryosuke Sato")

(homepage https://github.com/hopv/MoCHi)

(license "Apache-2.0")

(package
 (name mochi)
 (synopsis "MoCHi: Model Checker for Higher-Order Programs")
 (description "MoCHi is a software model checker for OCaml.
MoCHi is based on higher-order model checking, predicate abstraction, and CEGAR.")
 (depends
  (ocaml (and (>= 4.08.0) (< 5.2.0)))
  (dune (>= 3.6))
  (z3 (>= 4.8.9))
  (batteries (>= 3.7.1))
  ocamlfind
  ppx_deriving
  (ppxlib (= 0.25.1))
  yojson
  menhir
  fpat
  csisat
  atp
  (smtlib-utils (>= 0.3.1))
  ocamlgraph
  dune-build-info
  bos
  fmt
  re2
  tsort))

(using menhir 2.1)
