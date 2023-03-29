LANGUAGE=C++

all: build

build: $(LANGUAGE)/Makefile
	cd $(LANGUAGE)/ && (make; cd ..)

clean: $(LANGUAGE)/Makefile
	cd $(LANGUAGE)/ && (make clean; cd ..)

interpret: $(LANGUAGE)/Makefile
	cd $(LANGUAGE)/ && (make interpret; cd ..)

typecheck: $(LANGUAGE)/Makefile
	cd $(LANGUAGE)/ && (make typecheck; cd ..)

compile: $(LANGUAGE)/Makefile
	cd $(LANGUAGE)/ && (make compile; cd ..)

syntax-pdf: doc/Stella.pdf

doc/Stella.pdf: doc/Stella.tex
	latexmk -output-directory=doc/ -pdflatex doc/Stella.tex

doc/Stella.tex: Stella.cf
	bnfc --latex Stella.cf -o doc/

.PHONY: all build clean interpret typecheck compile syntax-pdf
