all: Stella/TestStella build/stella-interpreter

typecheck: build/stella-interpreter
	./build/stella-interpreter

interpret: build/stella-interpreter
	./build/stella-interpreter $(STELLA_FILE)

Stella/TestStella: ../Stella.cf
	mkdir -p Stella/
	cd Stella/ && (bnfc -m --cpp ../../Stella.cf -l -p Stella; cd ../)
	cd Stella/ && (make; cd ../)

build/stella-interpreter: Interpret.cpp TypeCheck.cpp TypeCheck.h Eval.cpp Eval.h Stella/TestStella
	cmake -S. -Bbuild
	cmake --build build/ --target stella-interpreter --

.PHONY: all typecheck interpret
