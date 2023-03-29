cmake_minimum_required(VERSION 3.10.0)
project(stella-interpreter VERSION 0.1.0)

set (Stella_Syntax
  Stella/Absyn.H
  Stella/Absyn.C
  Stella/Parser.H
  Stella/Parser.C
  Stella/ParserError.H
  Stella/Printer.H
  Stella/Printer.C
  Stella/Buffer.H
  Stella/Buffer.C
  Stella/Bison.H
  Stella/Lexer.C
)

set (SRCS
  Interpret.cpp
  Eval.h
  Eval.cpp
  TypeCheck.h
  TypeCheck.cpp
)

add_executable(stella-interpreter ${Stella_Syntax} ${SRCS})
set_property(TARGET stella-interpreter PROPERTY CXX_STANDARD 17)

set(CPACK_PROJECT_NAME ${PROJECT_NAME})
set(CPACK_PROJECT_VERSION ${PROJECT_VERSION})
include(CPack)
