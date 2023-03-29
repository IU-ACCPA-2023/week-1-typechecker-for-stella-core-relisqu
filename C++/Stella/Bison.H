/* A Bison parser, made by GNU Bison 3.8.2.  */

/* Bison interface for Yacc-like parsers in C

   Copyright (C) 1984, 1989-1990, 2000-2015, 2018-2021 Free Software Foundation,
   Inc.

   This program is free software: you can redistribute it and/or modify
   it under the terms of the GNU General Public License as published by
   the Free Software Foundation, either version 3 of the License, or
   (at your option) any later version.

   This program is distributed in the hope that it will be useful,
   but WITHOUT ANY WARRANTY; without even the implied warranty of
   MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
   GNU General Public License for more details.

   You should have received a copy of the GNU General Public License
   along with this program.  If not, see <https://www.gnu.org/licenses/>.  */

/* As a special exception, you may create a larger work that contains
   part or all of the Bison parser skeleton and distribute that work
   under terms of your choice, so long as that work isn't itself a
   parser generator using the skeleton or a modified version thereof
   as a parser skeleton.  Alternatively, if you modify or redistribute
   the parser skeleton itself, you may (at your option) remove this
   special exception, which will cause the skeleton and the resulting
   Bison output files to be licensed under the GNU General Public
   License without this special exception.

   This special exception was added by the Free Software Foundation in
   version 2.2 of Bison.  */

/* DO NOT RELY ON FEATURES THAT ARE NOT DOCUMENTED in the manual,
   especially those whose name start with YY_ or yy_.  They are
   private implementation details that can be changed or removed.  */

#ifndef YY_STELLA_BISON_H_INCLUDED
# define YY_STELLA_BISON_H_INCLUDED
/* Debug traces.  */
#ifndef YYDEBUG
# define YYDEBUG 1
#endif
#if YYDEBUG
extern int Stelladebug;
#endif

/* Token kinds.  */
#ifndef YYTOKENTYPE
# define YYTOKENTYPE
  enum yytokentype
  {
    YYEMPTY = -2,
    YYEOF = 0,                     /* "end of file"  */
    YYerror = 256,                 /* error  */
    YYUNDEF = 257,                 /* "invalid token"  */
    _ERROR_ = 258,                 /* _ERROR_  */
    _BANGEQ = 259,                 /* _BANGEQ  */
    _LPAREN = 260,                 /* _LPAREN  */
    _RPAREN = 261,                 /* _RPAREN  */
    _STAR = 262,                   /* _STAR  */
    _PLUS = 263,                   /* _PLUS  */
    _COMMA = 264,                  /* _COMMA  */
    _RARROW = 265,                 /* _RARROW  */
    _DOT = 266,                    /* _DOT  */
    _COLON = 267,                  /* _COLON  */
    _SEMI = 268,                   /* _SEMI  */
    _LT = 269,                     /* _LT  */
    _LDARROW = 270,                /* _LDARROW  */
    _SYMB_10 = 271,                /* _SYMB_10  */
    _EQ = 272,                     /* _EQ  */
    _DEQ = 273,                    /* _DEQ  */
    _RDARROW = 274,                /* _RDARROW  */
    _GT = 275,                     /* _GT  */
    _GTEQ = 276,                   /* _GTEQ  */
    _KW_Bool = 277,                /* _KW_Bool  */
    _SYMB_22 = 278,                /* _SYMB_22  */
    _SYMB_23 = 279,                /* _SYMB_23  */
    _SYMB_24 = 280,                /* _SYMB_24  */
    _KW_Nat = 281,                 /* _KW_Nat  */
    _SYMB_26 = 282,                /* _SYMB_26  */
    _SYMB_25 = 283,                /* _SYMB_25  */
    _SYMB_27 = 284,                /* _SYMB_27  */
    _KW_Unit = 285,                /* _KW_Unit  */
    _LBRACK = 286,                 /* _LBRACK  */
    _RBRACK = 287,                 /* _RBRACK  */
    _KW_and = 288,                 /* _KW_and  */
    _KW_as = 289,                  /* _KW_as  */
    _KW_cons = 290,                /* _KW_cons  */
    _KW_core = 291,                /* _KW_core  */
    _KW_else = 292,                /* _KW_else  */
    _KW_extend = 293,              /* _KW_extend  */
    _KW_false = 294,               /* _KW_false  */
    _KW_fix = 295,                 /* _KW_fix  */
    _KW_fn = 296,                  /* _KW_fn  */
    _KW_fold = 297,                /* _KW_fold  */
    _KW_if = 298,                  /* _KW_if  */
    _KW_in = 299,                  /* _KW_in  */
    _KW_inline = 300,              /* _KW_inline  */
    _KW_language = 301,            /* _KW_language  */
    _KW_let = 302,                 /* _KW_let  */
    _KW_match = 303,               /* _KW_match  */
    _KW_not = 304,                 /* _KW_not  */
    _KW_or = 305,                  /* _KW_or  */
    _KW_record = 306,              /* _KW_record  */
    _KW_return = 307,              /* _KW_return  */
    _KW_succ = 308,                /* _KW_succ  */
    _KW_then = 309,                /* _KW_then  */
    _KW_throws = 310,              /* _KW_throws  */
    _KW_true = 311,                /* _KW_true  */
    _KW_type = 312,                /* _KW_type  */
    _KW_unfold = 313,              /* _KW_unfold  */
    _KW_variant = 314,             /* _KW_variant  */
    _KW_with = 315,                /* _KW_with  */
    _LBRACE = 316,                 /* _LBRACE  */
    _SYMB_11 = 317,                /* _SYMB_11  */
    _RBRACE = 318,                 /* _RBRACE  */
    _KW_60 = 319,                  /* _KW_60  */
    T_ExtensionName = 320,         /* T_ExtensionName  */
    T_StellaIdent = 321,           /* T_StellaIdent  */
    _INTEGER_ = 322                /* _INTEGER_  */
  };
  typedef enum yytokentype yytoken_kind_t;
#endif

/* Value type.  */
#if ! defined YYSTYPE && ! defined YYSTYPE_IS_DECLARED
union YYSTYPE
{
#line 52 "Stella.y"

  int    _int;
  char   _char;
  double _double;
  char*  _string;
  Stella::Program* program_;
  Stella::ListStellaIdent* liststellaident_;
  Stella::LanguageDecl* languagedecl_;
  Stella::Extension* extension_;
  Stella::ListExtensionName* listextensionname_;
  Stella::ListExtension* listextension_;
  Stella::Decl* decl_;
  Stella::ListDecl* listdecl_;
  Stella::LocalDecl* localdecl_;
  Stella::ListLocalDecl* listlocaldecl_;
  Stella::Annotation* annotation_;
  Stella::ListAnnotation* listannotation_;
  Stella::ParamDecl* paramdecl_;
  Stella::ListParamDecl* listparamdecl_;
  Stella::ReturnType* returntype_;
  Stella::ThrowType* throwtype_;
  Stella::Expr* expr_;
  Stella::ListExpr* listexpr_;
  Stella::MatchCase* matchcase_;
  Stella::ListMatchCase* listmatchcase_;
  Stella::OptionalTyping* optionaltyping_;
  Stella::PatternData* patterndata_;
  Stella::ExprData* exprdata_;
  Stella::Pattern* pattern_;
  Stella::ListPattern* listpattern_;
  Stella::LabelledPattern* labelledpattern_;
  Stella::ListLabelledPattern* listlabelledpattern_;
  Stella::Binding* binding_;
  Stella::ListBinding* listbinding_;
  Stella::Type* type_;
  Stella::ListType* listtype_;
  Stella::VariantFieldType* variantfieldtype_;
  Stella::ListVariantFieldType* listvariantfieldtype_;
  Stella::RecordFieldType* recordfieldtype_;
  Stella::ListRecordFieldType* listrecordfieldtype_;
  Stella::Typing* typing_;

#line 174 "Bison.H"

};
typedef union YYSTYPE YYSTYPE;
# define YYSTYPE_IS_TRIVIAL 1
# define YYSTYPE_IS_DECLARED 1
#endif

/* Location type.  */
#if ! defined YYLTYPE && ! defined YYLTYPE_IS_DECLARED
typedef struct YYLTYPE YYLTYPE;
struct YYLTYPE
{
  int first_line;
  int first_column;
  int last_line;
  int last_column;
};
# define YYLTYPE_IS_DECLARED 1
# define YYLTYPE_IS_TRIVIAL 1
#endif




int Stellaparse (yyscan_t scanner, YYSTYPE *result);


#endif /* !YY_STELLA_BISON_H_INCLUDED  */
