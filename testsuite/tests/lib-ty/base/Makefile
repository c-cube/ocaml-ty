#########################################################################
#                                                                       #
#                                 OCaml                                 #
#                                                                       #
#                 Xavier Clerc, SED, INRIA Rocquencourt                 #
#                                                                       #
#   Copyright 2010 Institut National de Recherche en Informatique et    #
#   en Automatique.  All rights reserved.  This file is distributed     #
#   under the terms of the Q Public License version 1.0.                #
#                                                                       #
#########################################################################

ADD_COMPFLAGS=-rectypes

LIBRARIES=common

TESTS=\
  basic.ml \
  declaration.ml \
  introspection.ml \
  id.ml \
  external_ids.ml \
  caret.ml \
  equality.ml \
  printer.ml

BASEDIR=../../..
include $(BASEDIR)/makefiles/Makefile.several
include $(BASEDIR)/makefiles/Makefile.common

run-all: common.cma
run-file: common.cma

LIB_FILES=common

common.cma: $(LIB_FILES:=.cmo)
	@$(OCAMLC) -a -o $@ $(COMPFLAGS) $(ADD_COMPFLAGS) $<

#ifneq (${BYTECODE_ONLY},YES)

run-all: common.cma
run-file: common.cma

common.cmxa: $(LIB_FILES:=.cmx)
	@$(OCAMLOPT) -a -o $@ $(COMPFLAGS) $(ADD_COMPFLAGS) $<

#fi
