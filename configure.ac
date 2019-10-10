AC_INIT(MoCHi,0.1)

AC_PROG_CC

AC_PROG_OCAML
if test "$OCAMLC" = "no"; then
  AC_MSG_ERROR([OCaml compiler not found])
fi

AC_PROG_FINDLIB
if test "$OCAMLFIND" = "no"; then
  AC_MSG_ERROR([ocamlfind not found])
fi

AC_PROG_OCAMLLEX
if test "$OCAMLLEX" = "no"; then
  AC_MSG_ERROR([ocamllex not found])
fi

AC_PROG_OCAMLYACC
if test "$OCAMLYACC" = "no"; then
  AC_MSG_ERROR([ocamlyacc not found])
fi

AC_CHECK_OCAML_PKG([batteries])
if test "$OCAML_PKG_batteries" = "no"; then
  AC_MSG_ERROR([batteries not found])
fi

AC_CHECK_OCAML_PKG([ppx_deriving])
if test "$OCAML_PKG_ppx_deriving" = "no"; then
  AC_MSG_ERROR([ppx_deriving not found])
fi

AC_CHECK_OCAML_PKG([z3])
if test "$OCAML_PKG_Z3" = "no"; then
  AC_MSG_ERROR([Z3 not found])
fi

AC_CHECK_OCAML_PKG([yojson])
if test "$OCAML_PKG_yojson" = "no"; then
  AC_MSG_ERROR([yojson not found])
fi

AC_PATH_TOOL(CVC3, cvc3, [no], [$PATH:$PWD])
AC_SUBST(CVC3)

AC_PATH_TOOL(TRECS, trecs, [no], [$PATH:$PWD])
AC_SUBST(TRECS)

AC_PATH_TOOL(HORSAT, horsat, [no], [$PATH:$PWD])
AC_SUBST(HORSAT)

AC_PATH_TOOL(HORSAT2, horsat2, [no], [$PATH:$PWD])
AC_SUBST(HORSAT2)

AC_PATH_TOOL(HORSATP, horsatp, [no], [$PATH:$PWD])
AC_SUBST(HORSATP)

AC_PATH_TOOL(HORS_QUICKCHECK, hors_quickcheck, [no], [$PATH:$PWD])
AC_SUBST(HORS_QUICKCHECK)

AC_PATH_TOOL(HOICE, hoice, [no], [$PATH:$PWD])
AC_SUBST(HOICE)

AC_PATH_TOOL(Z3_BIN, z3, [no], [$PATH:$PWD])
AC_SUBST(Z3_BIN)

if test "$TRECS" = "no" -a "$HORSAT" = "no" -a "$HORSAT2" = "no" -a "$HORSATP" = "no"; then
  AC_MSG_ERROR([No model checker found])
fi

AC_PATH_TOOL(OMEGA, oc, [no], [$PATH:$PWD])
AC_SUBST(OMEGA)

AC_CHECK_PROG(GIT, git, git)
AC_SUBST(GIT)
AC_CHECK_FILE([.git], [], [GIT=""])

OCAML_VER=`ocamlc -version`
AC_SUBST(OCAML_VER)
OCAML_MAJOR_VER=`ocamlc -version | cut -d . -f 1,2`
AC_SUBST(OCAML_MAJOR_VER)

AC_CONFIG_FILES([Makefile.config mconfig.ml])
AC_OUTPUT
