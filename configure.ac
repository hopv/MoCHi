AC_INIT(MoCHi,0.1)

AC_PATH_TOOL(OCAMLC, ocamlc, [no], [$PATH:$PWD])
AC_SUBST(OCAMLC)

if test "$OCAMLC" = "no"; then
  AC_MSG_ERROR([OCaml not found])
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

AC_CHECK_PROG(DUNE, dune, dune)
AC_SUBST(DUNE)

AC_CHECK_PROG(MENHIR, menhir, menhir)

AC_CHECK_PROG(GIT, git, git)
AC_SUBST(GIT)
AC_CHECK_FILE([.git], [], [GIT=""])
if test -n "$GIT"; then
  GIT_SRC_FILES=`$GIT ls-files | grep '^src/' | grep -v src/cmd.ml | grep -v src/mochi.ml | sed 's/^src\///' | tr '\n' ' '`
  REV_DEPS="(deps    $GIT_SRC_FILES)"
fi
AC_SUBST(REV_DEPS)

OCAML_VER=`$OCAMLC -version`
OCAML_MAJOR_VER=`$OCAMLC -version | cut -d . -f 1,2`
SUPPORTED=`ls src/parser_wrapper_*.ml | sed -e 's/.*parser_wrapper_\(.*\)\.ml/\1/'`
if echo $SUPPORTED | grep -qsv $OCAML_MAJOR_VER; then
  AC_MSG_ERROR([OCaml $OCAML_VER is not supported])
fi


AC_CONFIG_FILES([src/mconfig.ml src/dune_inc])
AC_OUTPUT
