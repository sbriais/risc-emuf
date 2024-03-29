	ifdef	CROSS
OCAMLOPT=i686-w64-mingw32-ocamlopt
OCAMLC=i686-w64-mingw32-ocamlc
OCAMLDEP=i686-w64-mingw32-ocamldep
	else
OCAMLOPT=ocamlopt
OCAMLC=ocamlc
OCAMLDEP=ocamldep
	endif

INCL=-I +labltk

#OCAMLNLDFLAGS = -ccopt -static
OCAMLFLAGS=-unsafe -annot -warn-error +a -w +a-4-42-45

VERSION=0.1.2

SRCMLI=
SRCMLI+=

SRCML=version.ml
SRCML+=risc.ml
SRCML+=scanner.ml
SRCML+=parser.ml
SRCML+=codec.ml
SRCML+=gcmap.ml
SRCML+=emulator.ml
SRCML+=fast_emul.ml
SRCML+=gui.ml
SRCML+=main.ml

SRCS=$(SRCML) $(SRCMLI)

PROJECT=risc-emuf

EXTRA=README.md Makefile

LIBS=bigarray labltk

BYTELIBS=$(LIBS:=.cma)
NATIVELIBS=$(LIBS:=.cmxa)

CMI=$(SRCMLI:.mli=.cmi)
CMO=$(SRCML:.ml=.cmo)
CMX=$(SRCML:.ml=.cmx)

all: .depend $(PROJECT).native $(PROJECT).byte

.PHONY: all clean dist

$(PROJECT).native: $(CMX)
	$(OCAMLOPT) $(INCL) -o $@ $(NATIVELIBS) $^

$(PROJECT).byte: $(CMO)
	$(OCAMLC) $(INCL) -o $@ $(BYTELIBS) $^

fast_emul.ml: fast_emul.cpp
	$(CPP) -P $^ > $@

version.ml: Makefile
	@echo "let date_of_compile=\""`date`"\";;" > $@
	@echo "let version=\""$(VERSION)"\";;" >> $@
	@echo "let build_info=\""`uname -msrn`"\";;" >> $@
	@echo "let revision=\""`git log -1 --format="%h"`"\";;" >> $@

dist: $(SRCS) $(EXTRA)
	mkdir $(PROJECT)
	cp $(SRCS) $(EXTRA) $(PROJECT)
	tar cfvz $(PROJECT)-$(VERSION).tar.gz $(PROJECT)
	rm -rf $(PROJECT)

%.cmo: %.ml
	$(OCAMLC) $(INCL) -c $(OCAMLFLAGS) -o $@ $<

%.cmi: %.mli
	$(OCAMLC) $(INCL) -c $(OCAMLFLAGS) -o $@ $<

%.cmx: %.ml
	$(OCAMLOPT) $(INCL) -c $(OCAMLFLAGS) -o $@ $<

clean:
	rm -f $(CMI) $(CMO) $(CMX) $(SRCML:.ml=.o) $(SRCML:.ml=.annot) $(SRCML:.ml=.cmi) version.ml fast_emul.ml $(PROJECT).byte $(PROJECT).native *~

.depend: $(SRCS)
	$(OCAMLDEP) $(INCL) $(SRCS) > .depend

-include .depend
