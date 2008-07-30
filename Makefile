##########################################################################
##  v      #                  The Coq Proof Assistant                   ##
## <O___,, # CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud ##
##   \VV/  #                                                            ##
##    //   #   Makefile automagically generated by coq_makefile V8.2    ##
##########################################################################

# WARNING
#
# This Makefile has been automagically generated
# Edit at your own risks !
#
# END OF WARNING

#
# This Makefile was generated by the command line :
# coq_makefile -f Make -o Makefile 
#

#########################
#                       #
# Libraries definition. #
#                       #
#########################

CAMLP4LIB:=$(shell $(CAMLBIN)camlp5 -where 2> /dev/null || $(CAMLBIN)camlp4 -where)
OCAMLLIBS:=-I $(CAMLP4LIB) -I ./Rewrite/LeibnizRewrite/MLstuff\
  -I ./Rewrite/GenericRewrite/genMLstuff\
  -I ./Rewrite/LeibnizRewrite/AC\
  -I ./Rewrite/LeibnizRewrite/HS\
  -I ./Rewrite/GenericRewrite/HeadSimpl
COQLIBS:= -R . Rational
COQDOCLIBS:=-R . Rational

##########################
#                        #
# Variables definitions. #
#                        #
##########################

CAMLP4:=$(notdir $(CAMLP4LIB))
COQSRC:=$(COQTOP)
COQSRCLIBS:=-I $(COQTOP)/kernel -I $(COQTOP)/lib \
  -I $(COQTOP)/library -I $(COQTOP)/parsing \
  -I $(COQTOP)/pretyping -I $(COQTOP)/interp \
  -I $(COQTOP)/proofs -I $(COQTOP)/tactics \
  -I $(COQTOP)/toplevel -I $(COQTOP)/contrib/cc \
  -I $(COQTOP)/contrib/dp -I $(COQTOP)/contrib/extraction \
  -I $(COQTOP)/contrib/field -I $(COQTOP)/contrib/firstorder \
  -I $(COQTOP)/contrib/fourier -I $(COQTOP)/contrib/funind \
  -I $(COQTOP)/contrib/interface -I $(COQTOP)/contrib/jprover \
  -I $(COQTOP)/contrib/micromega -I $(COQTOP)/contrib/omega \
  -I $(COQTOP)/contrib/ring -I $(COQTOP)/contrib/romega \
  -I $(COQTOP)/contrib/rtauto -I $(COQTOP)/contrib/setoid_ring \
  -I $(COQTOP)/contrib/subtac -I $(COQTOP)/contrib/xml \
  -I $(CAMLP4LIB)
ZFLAGS:=$(OCAMLLIBS) $(COQSRCLIBS)
override OPT:=-byte
COQFLAGS:=-q $(OPT) $(COQLIBS) $(OTHERFLAGS) $(COQ_XML)
COQC:=$(COQBIN)coqc
COQDEP:=$(COQBIN)coqdep -c
GALLINA:=$(COQBIN)gallina
COQDOC:=$(COQBIN)coqdoc
CAMLC:=$(CAMLBIN)ocamlc -rectypes -c
CAMLOPTC:=$(CAMLBIN)ocamlopt -rectypes -c
CAMLLINK:=$(CAMLBIN)ocamlc -rectypes
CAMLOPTLINK:=$(CAMLBIN)ocamlopt -rectypes
GRAMMARS:=grammar.cma
CAMLP4EXTEND:=pa_extend.cmo pa_macro.cmo q_MLast.cmo
PP:=-pp "$(CAMLBIN)$(CAMLP4)o -I . -I $(COQTOP)/parsing $(CAMLP4EXTEND) $(GRAMMARS) -impl"

###################################
#                                 #
# Definition of the "all" target. #
#                                 #
###################################

VFILES:=./Natural/NATURAL.v\
  ./Natural/nat.v\
  ./Rewrite/GenericRewrite/HeadSimpl/HeadSimpl.v\
  ./Rewrite/LeibnizRewrite/HS/HS.v\
  ./Rewrite/LeibnizRewrite/AC/AC.v\
  ./Subset/subset.v\
  ./Rational/minus.v\
  ./Rational/rational.v\
  ./Rational/PlusQ.v\
  ./Rational/rat.v\
  ./Rational/MultQ.v\
  ./Rational/rational_defs.v\
  ./Rational/Z_to_Q.v\
  ./Util/productSyntax.v\
  ./Quotient/quotient.v\
  ./Quotient/extensionality.v\
  ./Integer/int.v\
  ./Integer/intnumbers.v\
  ./Integer/leZproperties.v\
  ./Integer/integer.v\
  ./Integer/PlusZ.v\
  ./Integer/leZ.v\
  ./Integer/integer_defs.v\
  ./Integer/Absz.v\
  ./Integer/MultZ.v
VOFILES:=$(VFILES:.v=.vo)
GLOBFILES:=$(VFILES:.v=.glob)
VIFILES:=$(VFILES:.v=.vi)
GFILES:=$(VFILES:.v=.g)
HTMLFILES:=$(VFILES:.v=.html)
GHTMLFILES:=$(VFILES:.v=.g.html)
MLFILES:=./Rewrite/LeibnizRewrite/HS/hS.ml\
  ./Rewrite/LeibnizRewrite/HS/hS_tac.ml\
  ./Rewrite/LeibnizRewrite/AC/aC.ml\
  ./Rewrite/LeibnizRewrite/AC/aC_tac.ml\
  ./Rewrite/LeibnizRewrite/MLstuff/sort_tac.ml\
  ./Rewrite/LeibnizRewrite/MLstuff/struct.ml\
  ./Rewrite/GenericRewrite/genMLstuff/frame.ml\
  ./Rewrite/GenericRewrite/genMLstuff/basic.ml\
  ./Rewrite/GenericRewrite/HeadSimpl/main.ml\
  ./Rewrite/GenericRewrite/HeadSimpl/tacentry.ml
CMOFILES:=$(MLFILES:.ml=.cmo)

all: $(VOFILES) $(CMOFILES) 
spec: $(VIFILES)

gallina: $(GFILES)

html: $(GLOBFILES) $(VFILES)
	- mkdir html
	$(COQDOC) -toc -html $(COQDOCLIBS) -d html $(VFILES)

gallinahtml: $(GLOBFILES) $(VFILES)
	- mkdir html
	$(COQDOC) -toc -html -g $(COQDOCLIBS) -d html $(VFILES)

all.ps: $(VFILES)
	$(COQDOC) -toc -ps $(COQDOCLIBS) -o $@ `$(COQDEP) -sort -suffix .v $(VFILES)`

all-gal.ps: $(VFILES)
	$(COQDOC) -toc -ps -g $(COQDOCLIBS) -o $@ `$(COQDEP) -sort -suffix .v $(VFILES)`



####################
#                  #
# Special targets. #
#                  #
####################

.PHONY: all opt byte archclean clean install depend html

%.cmi: %.mli
	$(CAMLC) $(ZDEBUG) $(ZFLAGS) $<

%.cmo: %.ml
	$(CAMLC) $(ZDEBUG) $(ZFLAGS) $(PP) $<

%.cmx: %.ml
	$(CAMLOPTC) $(ZDEBUG) $(ZFLAGS) $(PP) $<

%.ml.d: %.ml
	$(CAMLBIN)ocamldep -slash $(ZFLAGS) $(PP) "$<" > "$@"

%.vo %.glob: %.v
	$(COQC) -dump-glob $*.glob $(COQDEBUG) $(COQFLAGS) $*

%.vi: %.v
	$(COQC) -i $(COQDEBUG) $(COQFLAGS) $*

%.g: %.v
	$(GALLINA) $<

%.tex: %.v
	$(COQDOC) -latex $< -o $@

%.html: %.v %.glob
	$(COQDOC) -glob-from $*.glob  -html $< -o $@

%.g.tex: %.v
	$(COQDOC) -latex -g $< -o $@

%.g.html: %.v %.glob
	$(COQDOC) -glob-from $*.glob -html -g $< -o $@

%.v.d: %.v
	$(COQDEP) -glob -slash $(COQLIBS) "$<" > "$@" || ( RV=$$?; rm -f "$@"; exit $${RV} )

byte:
	$(MAKE) all "OPT:=-byte"

opt:
	$(MAKE) all "OPT:=-byte"

install:
	mkdir -p `$(COQC) -where`/user-contrib
	cp -f $(VOFILES) `$(COQC) -where`/user-contrib
	cp -f *.cmo `$(COQC) -where`/user-contrib

Makefile: Make
	mv -f Makefile Makefile.bak
	$(COQBIN)coq_makefile -f Make -o Makefile


clean:
	rm -f *.cmo *.cmi *.cmx *.o $(VOFILES) $(VIFILES) $(GFILES) *~
	rm -f all.ps all-gal.ps all.glob $(VFILES:.v=.glob) $(HTMLFILES) $(GHTMLFILES) $(VFILES:.v=.tex) $(VFILES:.v=.g.tex) $(VFILES:.v=.v.d)
	rm -f $(CMOFILES) $(MLFILES:.ml=.cmi) $(MLFILES:.ml=.ml.d)
	- rm -rf html

archclean:
	rm -f *.cmx *.o


-include $(VFILES:.v=.v.d)
.SECONDARY: $(VFILES:.v=.v.d)

-include $(MLFILES:.ml=.ml.d)
.SECONDARY: $(MLFILES:.ml=.ml.d)

# WARNING
#
# This Makefile has been automagically generated
# Edit at your own risks !
#
# END OF WARNING

