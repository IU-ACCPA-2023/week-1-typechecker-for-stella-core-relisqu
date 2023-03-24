OCAMLC=ocamlc
OCAMLCFLAGS=

all: src/Stella/TestStella src/Interpret

typecheck: src/Interpret
	./src/Interpret

interpret: src/Interpret
	./src/Interpret $(STELLA_FILE)

src/Stella/TestStella: ../Stella.cf
	bnfc -o src/Stella/ -m --ocaml ../Stella.cf
	cd src/Stella && (make; cd ../../)

src/Interpret: src/Interpret.ml src/TypeCheck.ml src/Eval.ml
	cd src/ && ($(OCAMLC) $(OCAMLCFLAGS) -I Stella/ -o Interpret Stella/BNFC_Util.ml Stella/AbsStella.ml Stella/SkelStella.ml Stella/ShowStella.ml Stella/PrintStella.ml Stella/ParStella.mli Stella/ParStella.ml Stella/LexStella.ml Eval.ml TypeCheck.ml Interpret.ml; cd ../)

.PHONY: all typecheck interpret
