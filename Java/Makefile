all: src/stella/Test.class src/Interpret.class

typecheck: src/Interpret.class
	java -cp "${CLASSPATH}:src/" Interpret

interpret: src/Interpret.class
	java -cp "${CLASSPATH}:src/" Interpret $(STELLA_FILE)

src/stella/Test.class: ../Stella.cf
	mkdir -p src/
	cd src/ && (bnfc -m --java --antlr ../../Stella.cf -l; cd ../)
	cd src/ && (make; cd ../)

src/Interpret.class: src/Interpret.java src/compiler/TypeCheck.java src/compiler/Eval.java src/stella/Test.class
	javac -sourcepath src/ src/Interpret.java

.PHONY: all typecheck interpret
