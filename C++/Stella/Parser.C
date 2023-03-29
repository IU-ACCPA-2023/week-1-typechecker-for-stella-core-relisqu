/* A Bison parser, made by GNU Bison 3.8.2.  */

/* Bison implementation for Yacc-like parsers in C

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

/* C LALR(1) parser skeleton written by Richard Stallman, by
   simplifying the original so-called "semantic" parser.  */

/* DO NOT RELY ON FEATURES THAT ARE NOT DOCUMENTED in the manual,
   especially those whose name start with YY_ or yy_.  They are
   private implementation details that can be changed or removed.  */

/* All symbols defined below should begin with yy or YY, to avoid
   infringing on user name space.  This should be done even for local
   variables, as they might otherwise be expanded by user macros.
   There are some unavoidable exceptions within include files to
   define necessary library symbols; they are noted "INFRINGES ON
   USER NAME SPACE" below.  */

/* Identify Bison output, and Bison version.  */
#define YYBISON 30802

/* Bison version string.  */
#define YYBISON_VERSION "3.8.2"

/* Skeleton name.  */
#define YYSKELETON_NAME "yacc.c"

/* Pure parsers.  */
#define YYPURE 1

/* Push parsers.  */
#define YYPUSH 0

/* Pull parsers.  */
#define YYPULL 1


/* Substitute the variable and function names.  */
#define yyparse         Stellaparse
#define yylex           Stellalex
#define yyerror         Stellaerror
#define yydebug         Stelladebug
#define yynerrs         Stellanerrs

/* First part of user prologue.  */
#line 22 "Stella.y"

/* Begin C preamble code */

#include <algorithm> /* for std::reverse */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include "Absyn.H"

#define YYMAXDEPTH 10000000

/* The type yyscan_t is defined by flex, but we need it in the parser already. */
#ifndef YY_TYPEDEF_YY_SCANNER_T
#define YY_TYPEDEF_YY_SCANNER_T
typedef void* yyscan_t;
#endif

typedef struct yy_buffer_state *YY_BUFFER_STATE;
extern YY_BUFFER_STATE Stella_scan_string(const char *str, yyscan_t scanner);
extern void Stella_delete_buffer(YY_BUFFER_STATE buf, yyscan_t scanner);

extern void Stellalex_destroy(yyscan_t scanner);
extern char* Stellaget_text(yyscan_t scanner);

extern yyscan_t Stella_initialize_lexer(FILE * inp);

/* End C preamble code */

#line 105 "Parser.C"

# ifndef YY_CAST
#  ifdef __cplusplus
#   define YY_CAST(Type, Val) static_cast<Type> (Val)
#   define YY_REINTERPRET_CAST(Type, Val) reinterpret_cast<Type> (Val)
#  else
#   define YY_CAST(Type, Val) ((Type) (Val))
#   define YY_REINTERPRET_CAST(Type, Val) ((Type) (Val))
#  endif
# endif
# ifndef YY_NULLPTR
#  if defined __cplusplus
#   if 201103L <= __cplusplus
#    define YY_NULLPTR nullptr
#   else
#    define YY_NULLPTR 0
#   endif
#  else
#   define YY_NULLPTR ((void*)0)
#  endif
# endif

#include "Bison.H"
/* Symbol kind.  */
enum yysymbol_kind_t
{
  YYSYMBOL_YYEMPTY = -2,
  YYSYMBOL_YYEOF = 0,                      /* "end of file"  */
  YYSYMBOL_YYerror = 1,                    /* error  */
  YYSYMBOL_YYUNDEF = 2,                    /* "invalid token"  */
  YYSYMBOL__ERROR_ = 3,                    /* _ERROR_  */
  YYSYMBOL__BANGEQ = 4,                    /* _BANGEQ  */
  YYSYMBOL__LPAREN = 5,                    /* _LPAREN  */
  YYSYMBOL__RPAREN = 6,                    /* _RPAREN  */
  YYSYMBOL__STAR = 7,                      /* _STAR  */
  YYSYMBOL__PLUS = 8,                      /* _PLUS  */
  YYSYMBOL__COMMA = 9,                     /* _COMMA  */
  YYSYMBOL__RARROW = 10,                   /* _RARROW  */
  YYSYMBOL__DOT = 11,                      /* _DOT  */
  YYSYMBOL__COLON = 12,                    /* _COLON  */
  YYSYMBOL__SEMI = 13,                     /* _SEMI  */
  YYSYMBOL__LT = 14,                       /* _LT  */
  YYSYMBOL__LDARROW = 15,                  /* _LDARROW  */
  YYSYMBOL__SYMB_10 = 16,                  /* _SYMB_10  */
  YYSYMBOL__EQ = 17,                       /* _EQ  */
  YYSYMBOL__DEQ = 18,                      /* _DEQ  */
  YYSYMBOL__RDARROW = 19,                  /* _RDARROW  */
  YYSYMBOL__GT = 20,                       /* _GT  */
  YYSYMBOL__GTEQ = 21,                     /* _GTEQ  */
  YYSYMBOL__KW_Bool = 22,                  /* _KW_Bool  */
  YYSYMBOL__SYMB_22 = 23,                  /* _SYMB_22  */
  YYSYMBOL__SYMB_23 = 24,                  /* _SYMB_23  */
  YYSYMBOL__SYMB_24 = 25,                  /* _SYMB_24  */
  YYSYMBOL__KW_Nat = 26,                   /* _KW_Nat  */
  YYSYMBOL__SYMB_26 = 27,                  /* _SYMB_26  */
  YYSYMBOL__SYMB_25 = 28,                  /* _SYMB_25  */
  YYSYMBOL__SYMB_27 = 29,                  /* _SYMB_27  */
  YYSYMBOL__KW_Unit = 30,                  /* _KW_Unit  */
  YYSYMBOL__LBRACK = 31,                   /* _LBRACK  */
  YYSYMBOL__RBRACK = 32,                   /* _RBRACK  */
  YYSYMBOL__KW_and = 33,                   /* _KW_and  */
  YYSYMBOL__KW_as = 34,                    /* _KW_as  */
  YYSYMBOL__KW_cons = 35,                  /* _KW_cons  */
  YYSYMBOL__KW_core = 36,                  /* _KW_core  */
  YYSYMBOL__KW_else = 37,                  /* _KW_else  */
  YYSYMBOL__KW_extend = 38,                /* _KW_extend  */
  YYSYMBOL__KW_false = 39,                 /* _KW_false  */
  YYSYMBOL__KW_fix = 40,                   /* _KW_fix  */
  YYSYMBOL__KW_fn = 41,                    /* _KW_fn  */
  YYSYMBOL__KW_fold = 42,                  /* _KW_fold  */
  YYSYMBOL__KW_if = 43,                    /* _KW_if  */
  YYSYMBOL__KW_in = 44,                    /* _KW_in  */
  YYSYMBOL__KW_inline = 45,                /* _KW_inline  */
  YYSYMBOL__KW_language = 46,              /* _KW_language  */
  YYSYMBOL__KW_let = 47,                   /* _KW_let  */
  YYSYMBOL__KW_match = 48,                 /* _KW_match  */
  YYSYMBOL__KW_not = 49,                   /* _KW_not  */
  YYSYMBOL__KW_or = 50,                    /* _KW_or  */
  YYSYMBOL__KW_record = 51,                /* _KW_record  */
  YYSYMBOL__KW_return = 52,                /* _KW_return  */
  YYSYMBOL__KW_succ = 53,                  /* _KW_succ  */
  YYSYMBOL__KW_then = 54,                  /* _KW_then  */
  YYSYMBOL__KW_throws = 55,                /* _KW_throws  */
  YYSYMBOL__KW_true = 56,                  /* _KW_true  */
  YYSYMBOL__KW_type = 57,                  /* _KW_type  */
  YYSYMBOL__KW_unfold = 58,                /* _KW_unfold  */
  YYSYMBOL__KW_variant = 59,               /* _KW_variant  */
  YYSYMBOL__KW_with = 60,                  /* _KW_with  */
  YYSYMBOL__LBRACE = 61,                   /* _LBRACE  */
  YYSYMBOL__SYMB_11 = 62,                  /* _SYMB_11  */
  YYSYMBOL__RBRACE = 63,                   /* _RBRACE  */
  YYSYMBOL__KW_60 = 64,                    /* _KW_60  */
  YYSYMBOL_T_ExtensionName = 65,           /* T_ExtensionName  */
  YYSYMBOL_T_StellaIdent = 66,             /* T_StellaIdent  */
  YYSYMBOL__INTEGER_ = 67,                 /* _INTEGER_  */
  YYSYMBOL_YYACCEPT = 68,                  /* $accept  */
  YYSYMBOL_Program = 69,                   /* Program  */
  YYSYMBOL_LanguageDecl = 70,              /* LanguageDecl  */
  YYSYMBOL_Extension = 71,                 /* Extension  */
  YYSYMBOL_ListExtensionName = 72,         /* ListExtensionName  */
  YYSYMBOL_ListExtension = 73,             /* ListExtension  */
  YYSYMBOL_Decl = 74,                      /* Decl  */
  YYSYMBOL_ListDecl = 75,                  /* ListDecl  */
  YYSYMBOL_Annotation = 76,                /* Annotation  */
  YYSYMBOL_ListAnnotation = 77,            /* ListAnnotation  */
  YYSYMBOL_ParamDecl = 78,                 /* ParamDecl  */
  YYSYMBOL_ListParamDecl = 79,             /* ListParamDecl  */
  YYSYMBOL_ReturnType = 80,                /* ReturnType  */
  YYSYMBOL_ThrowType = 81,                 /* ThrowType  */
  YYSYMBOL_Expr = 82,                      /* Expr  */
  YYSYMBOL_ListExpr = 83,                  /* ListExpr  */
  YYSYMBOL_MatchCase = 84,                 /* MatchCase  */
  YYSYMBOL_ListMatchCase = 85,             /* ListMatchCase  */
  YYSYMBOL_OptionalTyping = 86,            /* OptionalTyping  */
  YYSYMBOL_PatternData = 87,               /* PatternData  */
  YYSYMBOL_ExprData = 88,                  /* ExprData  */
  YYSYMBOL_Pattern = 89,                   /* Pattern  */
  YYSYMBOL_ListPattern = 90,               /* ListPattern  */
  YYSYMBOL_LabelledPattern = 91,           /* LabelledPattern  */
  YYSYMBOL_ListLabelledPattern = 92,       /* ListLabelledPattern  */
  YYSYMBOL_Binding = 93,                   /* Binding  */
  YYSYMBOL_ListBinding = 94,               /* ListBinding  */
  YYSYMBOL_Expr1 = 95,                     /* Expr1  */
  YYSYMBOL_Expr2 = 96,                     /* Expr2  */
  YYSYMBOL_Expr3 = 97,                     /* Expr3  */
  YYSYMBOL_Expr4 = 98,                     /* Expr4  */
  YYSYMBOL_Expr5 = 99,                     /* Expr5  */
  YYSYMBOL_Expr6 = 100,                    /* Expr6  */
  YYSYMBOL_Type = 101,                     /* Type  */
  YYSYMBOL_Type1 = 102,                    /* Type1  */
  YYSYMBOL_Type2 = 103,                    /* Type2  */
  YYSYMBOL_Type3 = 104,                    /* Type3  */
  YYSYMBOL_ListType = 105,                 /* ListType  */
  YYSYMBOL_VariantFieldType = 106,         /* VariantFieldType  */
  YYSYMBOL_ListVariantFieldType = 107,     /* ListVariantFieldType  */
  YYSYMBOL_RecordFieldType = 108,          /* RecordFieldType  */
  YYSYMBOL_ListRecordFieldType = 109       /* ListRecordFieldType  */
};
typedef enum yysymbol_kind_t yysymbol_kind_t;


/* Second part of user prologue.  */
#line 95 "Stella.y"

void yyerror(YYLTYPE *loc, yyscan_t scanner, YYSTYPE *result, const char *msg)
{
  fprintf(stderr, "error: %d,%d: %s at %s\n",
    loc->first_line, loc->first_column, msg, Stellaget_text(scanner));
}

int yyparse(yyscan_t scanner, YYSTYPE *result);

extern int yylex(YYSTYPE *lvalp, YYLTYPE *llocp, yyscan_t scanner);

#line 260 "Parser.C"


#ifdef short
# undef short
#endif

/* On compilers that do not define __PTRDIFF_MAX__ etc., make sure
   <limits.h> and (if available) <stdint.h> are included
   so that the code can choose integer types of a good width.  */

#ifndef __PTRDIFF_MAX__
# include <limits.h> /* INFRINGES ON USER NAME SPACE */
# if defined __STDC_VERSION__ && 199901 <= __STDC_VERSION__
#  include <stdint.h> /* INFRINGES ON USER NAME SPACE */
#  define YY_STDINT_H
# endif
#endif

/* Narrow types that promote to a signed type and that can represent a
   signed or unsigned integer of at least N bits.  In tables they can
   save space and decrease cache pressure.  Promoting to a signed type
   helps avoid bugs in integer arithmetic.  */

#ifdef __INT_LEAST8_MAX__
typedef __INT_LEAST8_TYPE__ yytype_int8;
#elif defined YY_STDINT_H
typedef int_least8_t yytype_int8;
#else
typedef signed char yytype_int8;
#endif

#ifdef __INT_LEAST16_MAX__
typedef __INT_LEAST16_TYPE__ yytype_int16;
#elif defined YY_STDINT_H
typedef int_least16_t yytype_int16;
#else
typedef short yytype_int16;
#endif

/* Work around bug in HP-UX 11.23, which defines these macros
   incorrectly for preprocessor constants.  This workaround can likely
   be removed in 2023, as HPE has promised support for HP-UX 11.23
   (aka HP-UX 11i v2) only through the end of 2022; see Table 2 of
   <https://h20195.www2.hpe.com/V2/getpdf.aspx/4AA4-7673ENW.pdf>.  */
#ifdef __hpux
# undef UINT_LEAST8_MAX
# undef UINT_LEAST16_MAX
# define UINT_LEAST8_MAX 255
# define UINT_LEAST16_MAX 65535
#endif

#if defined __UINT_LEAST8_MAX__ && __UINT_LEAST8_MAX__ <= __INT_MAX__
typedef __UINT_LEAST8_TYPE__ yytype_uint8;
#elif (!defined __UINT_LEAST8_MAX__ && defined YY_STDINT_H \
       && UINT_LEAST8_MAX <= INT_MAX)
typedef uint_least8_t yytype_uint8;
#elif !defined __UINT_LEAST8_MAX__ && UCHAR_MAX <= INT_MAX
typedef unsigned char yytype_uint8;
#else
typedef short yytype_uint8;
#endif

#if defined __UINT_LEAST16_MAX__ && __UINT_LEAST16_MAX__ <= __INT_MAX__
typedef __UINT_LEAST16_TYPE__ yytype_uint16;
#elif (!defined __UINT_LEAST16_MAX__ && defined YY_STDINT_H \
       && UINT_LEAST16_MAX <= INT_MAX)
typedef uint_least16_t yytype_uint16;
#elif !defined __UINT_LEAST16_MAX__ && USHRT_MAX <= INT_MAX
typedef unsigned short yytype_uint16;
#else
typedef int yytype_uint16;
#endif

#ifndef YYPTRDIFF_T
# if defined __PTRDIFF_TYPE__ && defined __PTRDIFF_MAX__
#  define YYPTRDIFF_T __PTRDIFF_TYPE__
#  define YYPTRDIFF_MAXIMUM __PTRDIFF_MAX__
# elif defined PTRDIFF_MAX
#  ifndef ptrdiff_t
#   include <stddef.h> /* INFRINGES ON USER NAME SPACE */
#  endif
#  define YYPTRDIFF_T ptrdiff_t
#  define YYPTRDIFF_MAXIMUM PTRDIFF_MAX
# else
#  define YYPTRDIFF_T long
#  define YYPTRDIFF_MAXIMUM LONG_MAX
# endif
#endif

#ifndef YYSIZE_T
# ifdef __SIZE_TYPE__
#  define YYSIZE_T __SIZE_TYPE__
# elif defined size_t
#  define YYSIZE_T size_t
# elif defined __STDC_VERSION__ && 199901 <= __STDC_VERSION__
#  include <stddef.h> /* INFRINGES ON USER NAME SPACE */
#  define YYSIZE_T size_t
# else
#  define YYSIZE_T unsigned
# endif
#endif

#define YYSIZE_MAXIMUM                                  \
  YY_CAST (YYPTRDIFF_T,                                 \
           (YYPTRDIFF_MAXIMUM < YY_CAST (YYSIZE_T, -1)  \
            ? YYPTRDIFF_MAXIMUM                         \
            : YY_CAST (YYSIZE_T, -1)))

#define YYSIZEOF(X) YY_CAST (YYPTRDIFF_T, sizeof (X))


/* Stored state numbers (used for stacks). */
typedef yytype_int16 yy_state_t;

/* State numbers in computations.  */
typedef int yy_state_fast_t;

#ifndef YY_
# if defined YYENABLE_NLS && YYENABLE_NLS
#  if ENABLE_NLS
#   include <libintl.h> /* INFRINGES ON USER NAME SPACE */
#   define YY_(Msgid) dgettext ("bison-runtime", Msgid)
#  endif
# endif
# ifndef YY_
#  define YY_(Msgid) Msgid
# endif
#endif


#ifndef YY_ATTRIBUTE_PURE
# if defined __GNUC__ && 2 < __GNUC__ + (96 <= __GNUC_MINOR__)
#  define YY_ATTRIBUTE_PURE __attribute__ ((__pure__))
# else
#  define YY_ATTRIBUTE_PURE
# endif
#endif

#ifndef YY_ATTRIBUTE_UNUSED
# if defined __GNUC__ && 2 < __GNUC__ + (7 <= __GNUC_MINOR__)
#  define YY_ATTRIBUTE_UNUSED __attribute__ ((__unused__))
# else
#  define YY_ATTRIBUTE_UNUSED
# endif
#endif

/* Suppress unused-variable warnings by "using" E.  */
#if ! defined lint || defined __GNUC__
# define YY_USE(E) ((void) (E))
#else
# define YY_USE(E) /* empty */
#endif

/* Suppress an incorrect diagnostic about yylval being uninitialized.  */
#if defined __GNUC__ && ! defined __ICC && 406 <= __GNUC__ * 100 + __GNUC_MINOR__
# if __GNUC__ * 100 + __GNUC_MINOR__ < 407
#  define YY_IGNORE_MAYBE_UNINITIALIZED_BEGIN                           \
    _Pragma ("GCC diagnostic push")                                     \
    _Pragma ("GCC diagnostic ignored \"-Wuninitialized\"")
# else
#  define YY_IGNORE_MAYBE_UNINITIALIZED_BEGIN                           \
    _Pragma ("GCC diagnostic push")                                     \
    _Pragma ("GCC diagnostic ignored \"-Wuninitialized\"")              \
    _Pragma ("GCC diagnostic ignored \"-Wmaybe-uninitialized\"")
# endif
# define YY_IGNORE_MAYBE_UNINITIALIZED_END      \
    _Pragma ("GCC diagnostic pop")
#else
# define YY_INITIAL_VALUE(Value) Value
#endif
#ifndef YY_IGNORE_MAYBE_UNINITIALIZED_BEGIN
# define YY_IGNORE_MAYBE_UNINITIALIZED_BEGIN
# define YY_IGNORE_MAYBE_UNINITIALIZED_END
#endif
#ifndef YY_INITIAL_VALUE
# define YY_INITIAL_VALUE(Value) /* Nothing. */
#endif

#if defined __cplusplus && defined __GNUC__ && ! defined __ICC && 6 <= __GNUC__
# define YY_IGNORE_USELESS_CAST_BEGIN                          \
    _Pragma ("GCC diagnostic push")                            \
    _Pragma ("GCC diagnostic ignored \"-Wuseless-cast\"")
# define YY_IGNORE_USELESS_CAST_END            \
    _Pragma ("GCC diagnostic pop")
#endif
#ifndef YY_IGNORE_USELESS_CAST_BEGIN
# define YY_IGNORE_USELESS_CAST_BEGIN
# define YY_IGNORE_USELESS_CAST_END
#endif


#define YY_ASSERT(E) ((void) (0 && (E)))

#if !defined yyoverflow

/* The parser invokes alloca or malloc; define the necessary symbols.  */

# ifdef YYSTACK_USE_ALLOCA
#  if YYSTACK_USE_ALLOCA
#   ifdef __GNUC__
#    define YYSTACK_ALLOC __builtin_alloca
#   elif defined __BUILTIN_VA_ARG_INCR
#    include <alloca.h> /* INFRINGES ON USER NAME SPACE */
#   elif defined _AIX
#    define YYSTACK_ALLOC __alloca
#   elif defined _MSC_VER
#    include <malloc.h> /* INFRINGES ON USER NAME SPACE */
#    define alloca _alloca
#   else
#    define YYSTACK_ALLOC alloca
#    if ! defined _ALLOCA_H && ! defined EXIT_SUCCESS
#     include <stdlib.h> /* INFRINGES ON USER NAME SPACE */
      /* Use EXIT_SUCCESS as a witness for stdlib.h.  */
#     ifndef EXIT_SUCCESS
#      define EXIT_SUCCESS 0
#     endif
#    endif
#   endif
#  endif
# endif

# ifdef YYSTACK_ALLOC
   /* Pacify GCC's 'empty if-body' warning.  */
#  define YYSTACK_FREE(Ptr) do { /* empty */; } while (0)
#  ifndef YYSTACK_ALLOC_MAXIMUM
    /* The OS might guarantee only one guard page at the bottom of the stack,
       and a page size can be as small as 4096 bytes.  So we cannot safely
       invoke alloca (N) if N exceeds 4096.  Use a slightly smaller number
       to allow for a few compiler-allocated temporary stack slots.  */
#   define YYSTACK_ALLOC_MAXIMUM 4032 /* reasonable circa 2006 */
#  endif
# else
#  define YYSTACK_ALLOC YYMALLOC
#  define YYSTACK_FREE YYFREE
#  ifndef YYSTACK_ALLOC_MAXIMUM
#   define YYSTACK_ALLOC_MAXIMUM YYSIZE_MAXIMUM
#  endif
#  if (defined __cplusplus && ! defined EXIT_SUCCESS \
       && ! ((defined YYMALLOC || defined malloc) \
             && (defined YYFREE || defined free)))
#   include <stdlib.h> /* INFRINGES ON USER NAME SPACE */
#   ifndef EXIT_SUCCESS
#    define EXIT_SUCCESS 0
#   endif
#  endif
#  ifndef YYMALLOC
#   define YYMALLOC malloc
#   if ! defined malloc && ! defined EXIT_SUCCESS
void *malloc (YYSIZE_T); /* INFRINGES ON USER NAME SPACE */
#   endif
#  endif
#  ifndef YYFREE
#   define YYFREE free
#   if ! defined free && ! defined EXIT_SUCCESS
void free (void *); /* INFRINGES ON USER NAME SPACE */
#   endif
#  endif
# endif
#endif /* !defined yyoverflow */

#if (! defined yyoverflow \
     && (! defined __cplusplus \
         || (defined YYLTYPE_IS_TRIVIAL && YYLTYPE_IS_TRIVIAL \
             && defined YYSTYPE_IS_TRIVIAL && YYSTYPE_IS_TRIVIAL)))

/* A type that is properly aligned for any stack member.  */
union yyalloc
{
  yy_state_t yyss_alloc;
  YYSTYPE yyvs_alloc;
  YYLTYPE yyls_alloc;
};

/* The size of the maximum gap between one aligned stack and the next.  */
# define YYSTACK_GAP_MAXIMUM (YYSIZEOF (union yyalloc) - 1)

/* The size of an array large to enough to hold all stacks, each with
   N elements.  */
# define YYSTACK_BYTES(N) \
     ((N) * (YYSIZEOF (yy_state_t) + YYSIZEOF (YYSTYPE) \
             + YYSIZEOF (YYLTYPE)) \
      + 2 * YYSTACK_GAP_MAXIMUM)

# define YYCOPY_NEEDED 1

/* Relocate STACK from its old location to the new one.  The
   local variables YYSIZE and YYSTACKSIZE give the old and new number of
   elements in the stack, and YYPTR gives the new location of the
   stack.  Advance YYPTR to a properly aligned location for the next
   stack.  */
# define YYSTACK_RELOCATE(Stack_alloc, Stack)                           \
    do                                                                  \
      {                                                                 \
        YYPTRDIFF_T yynewbytes;                                         \
        YYCOPY (&yyptr->Stack_alloc, Stack, yysize);                    \
        Stack = &yyptr->Stack_alloc;                                    \
        yynewbytes = yystacksize * YYSIZEOF (*Stack) + YYSTACK_GAP_MAXIMUM; \
        yyptr += yynewbytes / YYSIZEOF (*yyptr);                        \
      }                                                                 \
    while (0)

#endif

#if defined YYCOPY_NEEDED && YYCOPY_NEEDED
/* Copy COUNT objects from SRC to DST.  The source and destination do
   not overlap.  */
# ifndef YYCOPY
#  if defined __GNUC__ && 1 < __GNUC__
#   define YYCOPY(Dst, Src, Count) \
      __builtin_memcpy (Dst, Src, YY_CAST (YYSIZE_T, (Count)) * sizeof (*(Src)))
#  else
#   define YYCOPY(Dst, Src, Count)              \
      do                                        \
        {                                       \
          YYPTRDIFF_T yyi;                      \
          for (yyi = 0; yyi < (Count); yyi++)   \
            (Dst)[yyi] = (Src)[yyi];            \
        }                                       \
      while (0)
#  endif
# endif
#endif /* !YYCOPY_NEEDED */

/* YYFINAL -- State number of the termination state.  */
#define YYFINAL  5
/* YYLAST -- Last index in YYTABLE.  */
#define YYLAST   332

/* YYNTOKENS -- Number of terminals.  */
#define YYNTOKENS  68
/* YYNNTS -- Number of nonterminals.  */
#define YYNNTS  42
/* YYNRULES -- Number of rules.  */
#define YYNRULES  130
/* YYNSTATES -- Number of states.  */
#define YYNSTATES  296

/* YYMAXUTOK -- Last valid token kind.  */
#define YYMAXUTOK   322


/* YYTRANSLATE(TOKEN-NUM) -- Symbol number corresponding to TOKEN-NUM
   as returned by yylex, with out-of-bounds checking.  */
#define YYTRANSLATE(YYX)                                \
  (0 <= (YYX) && (YYX) <= YYMAXUTOK                     \
   ? YY_CAST (yysymbol_kind_t, yytranslate[YYX])        \
   : YYSYMBOL_YYUNDEF)

/* YYTRANSLATE[TOKEN-NUM] -- Symbol number corresponding to TOKEN-NUM
   as returned by yylex.  */
static const yytype_int8 yytranslate[] =
{
       0,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     1,     2,     3,     4,
       5,     6,     7,     8,     9,    10,    11,    12,    13,    14,
      15,    16,    17,    18,    19,    20,    21,    22,    23,    24,
      25,    26,    27,    28,    29,    30,    31,    32,    33,    34,
      35,    36,    37,    38,    39,    40,    41,    42,    43,    44,
      45,    46,    47,    48,    49,    50,    51,    52,    53,    54,
      55,    56,    57,    58,    59,    60,    61,    62,    63,    64,
      65,    66,    67
};

#if YYDEBUG
/* YYRLINE[YYN] -- Source line where rule number YYN was defined.  */
static const yytype_int16 yyrline[] =
{
       0,   223,   223,   229,   231,   233,   234,   235,   237,   238,
     240,   241,   243,   244,   251,   253,   254,   256,   258,   259,
     260,   262,   263,   265,   266,   268,   269,   270,   272,   273,
     274,   276,   278,   279,   280,   282,   283,   285,   286,   288,
     289,   291,   292,   293,   294,   295,   296,   297,   298,   299,
     300,   301,   303,   304,   305,   307,   309,   310,   311,   313,
     315,   316,   317,   319,   320,   321,   322,   323,   324,   325,
     327,   328,   329,   330,   331,   332,   333,   334,   335,   336,
     338,   339,   340,   342,   343,   345,   346,   347,   348,   349,
     350,   351,   352,   353,   354,   355,   356,   357,   359,   360,
     361,   362,   363,   364,   365,   367,   368,   369,   371,   372,
     374,   375,   376,   377,   378,   380,   381,   382,   383,   384,
     386,   387,   388,   390,   392,   393,   394,   396,   398,   399,
     400
};
#endif

/** Accessing symbol of state STATE.  */
#define YY_ACCESSING_SYMBOL(State) YY_CAST (yysymbol_kind_t, yystos[State])

#if YYDEBUG || 0
/* The user-facing name of the symbol whose (internal) number is
   YYSYMBOL.  No bounds checking.  */
static const char *yysymbol_name (yysymbol_kind_t yysymbol) YY_ATTRIBUTE_UNUSED;

/* YYTNAME[SYMBOL-NUM] -- String name of the symbol SYMBOL-NUM.
   First, the terminals, then, starting at YYNTOKENS, nonterminals.  */
static const char *const yytname[] =
{
  "\"end of file\"", "error", "\"invalid token\"", "_ERROR_", "_BANGEQ",
  "_LPAREN", "_RPAREN", "_STAR", "_PLUS", "_COMMA", "_RARROW", "_DOT",
  "_COLON", "_SEMI", "_LT", "_LDARROW", "_SYMB_10", "_EQ", "_DEQ",
  "_RDARROW", "_GT", "_GTEQ", "_KW_Bool", "_SYMB_22", "_SYMB_23",
  "_SYMB_24", "_KW_Nat", "_SYMB_26", "_SYMB_25", "_SYMB_27", "_KW_Unit",
  "_LBRACK", "_RBRACK", "_KW_and", "_KW_as", "_KW_cons", "_KW_core",
  "_KW_else", "_KW_extend", "_KW_false", "_KW_fix", "_KW_fn", "_KW_fold",
  "_KW_if", "_KW_in", "_KW_inline", "_KW_language", "_KW_let", "_KW_match",
  "_KW_not", "_KW_or", "_KW_record", "_KW_return", "_KW_succ", "_KW_then",
  "_KW_throws", "_KW_true", "_KW_type", "_KW_unfold", "_KW_variant",
  "_KW_with", "_LBRACE", "_SYMB_11", "_RBRACE", "_KW_60",
  "T_ExtensionName", "T_StellaIdent", "_INTEGER_", "$accept", "Program",
  "LanguageDecl", "Extension", "ListExtensionName", "ListExtension",
  "Decl", "ListDecl", "Annotation", "ListAnnotation", "ParamDecl",
  "ListParamDecl", "ReturnType", "ThrowType", "Expr", "ListExpr",
  "MatchCase", "ListMatchCase", "OptionalTyping", "PatternData",
  "ExprData", "Pattern", "ListPattern", "LabelledPattern",
  "ListLabelledPattern", "Binding", "ListBinding", "Expr1", "Expr2",
  "Expr3", "Expr4", "Expr5", "Expr6", "Type", "Type1", "Type2", "Type3",
  "ListType", "VariantFieldType", "ListVariantFieldType",
  "RecordFieldType", "ListRecordFieldType", YY_NULLPTR
};

static const char *
yysymbol_name (yysymbol_kind_t yysymbol)
{
  return yytname[yysymbol];
}
#endif

#define YYPACT_NINF (-216)

#define yypact_value_is_default(Yyn) \
  ((Yyn) == YYPACT_NINF)

#define YYTABLE_NINF (-3)

#define yytable_value_is_error(Yyn) \
  0

/* YYPACT[STATE-NUM] -- Index in YYTABLE of the portion describing
   STATE-NUM.  */
static const yytype_int16 yypact[] =
{
     -19,   -11,    31,  -216,    21,  -216,    22,  -216,     5,    55,
       4,     2,  -216,     3,  -216,   -15,    62,  -216,    56,    20,
    -216,  -216,     2,   223,    82,  -216,   223,  -216,  -216,  -216,
     223,    87,    34,    81,   223,    32,  -216,  -216,  -216,    91,
    -216,    35,    94,    70,   223,    38,    42,   100,    48,   102,
     247,   103,   105,   111,  -216,  -216,   113,   110,   114,    63,
     115,   116,    66,   223,  -216,   223,  -216,   223,    35,   119,
     120,   223,    38,  -216,   223,  -216,    42,  -216,  -216,  -216,
    -216,  -216,   223,    77,   223,  -216,  -216,  -216,  -216,  -216,
     223,    72,  -216,  -216,  -216,   -38,   129,   129,    69,   131,
     132,   133,   135,   137,   138,   129,   139,  -216,   141,   142,
     117,   129,    85,   176,   150,    98,   157,  -216,   143,   129,
    -216,  -216,   153,  -216,   282,     9,   158,  -216,   162,   169,
     166,   129,   129,   129,   129,   129,   129,   170,   152,   129,
     129,    35,   223,   134,   172,   125,   129,   127,   129,   223,
     128,   145,   176,    54,   176,   176,   176,   176,   176,   223,
      54,    54,    54,   129,   -21,  -216,   129,   136,   188,   191,
     196,   200,   203,   204,   129,  -216,   210,   206,   208,   190,
     129,   129,   205,   214,   209,   221,   160,   225,   201,  -216,
    -216,    -2,     9,    -2,    -2,    -2,    -2,    -2,  -216,     9,
     158,   158,   229,  -216,  -216,  -216,  -216,  -216,  -216,  -216,
    -216,  -216,   129,  -216,   129,  -216,   177,    24,   202,   197,
     205,   180,   205,   242,  -216,   187,   245,  -216,   205,  -216,
    -216,   238,   192,   240,  -216,   129,   127,  -216,  -216,    24,
    -216,   248,   254,   211,   162,   129,   129,   256,   250,   259,
     233,   205,   213,   205,   207,   205,  -216,   129,  -216,  -216,
     162,   129,  -216,   129,  -216,  -216,  -216,   205,   218,   205,
    -216,   266,   264,   267,   220,   279,  -216,  -216,  -216,   285,
     275,  -216,  -216,  -216,   205,   205,   213,  -216,  -216,  -216,
     230,   286,  -216,  -216,  -216,  -216
};

/* YYDEFACT[STATE-NUM] -- Default reduction number in state STATE-NUM.
   Performed when YYTABLE does not specify something else to do.  Zero
   means the default is an error.  */
static const yytype_uint8 yydefact[] =
{
       0,     0,     0,     8,     0,     1,    12,     3,     0,     0,
      15,     5,     9,     0,    13,     0,     6,     4,     0,     0,
      14,    16,     5,     0,     0,     7,     0,   115,   116,   117,
       0,     0,     0,     0,   120,     0,   118,    11,   107,   109,
     114,    18,     0,     0,   120,   128,   124,   121,     0,     0,
       0,     0,    19,     0,   119,   113,     0,     0,   129,     0,
      35,   125,     0,   120,   110,     0,   108,     0,    18,    21,
       0,     0,   128,   111,     0,   123,   124,   112,   122,   106,
      17,    20,     0,    23,     0,   127,   130,    36,   126,    22,
       0,     0,   105,    24,    12,    15,     0,     0,     0,     0,
       0,     0,     0,     0,     0,    28,     0,   101,     0,     0,
       0,     0,     0,     0,     0,     0,     0,   100,     0,    28,
     103,   102,     0,    27,    69,    79,    82,    84,    97,     0,
      39,     0,     0,     0,     0,     0,     0,    29,     0,     0,
       0,    18,     0,     0,     0,     0,     0,    60,     0,     0,
       0,     0,     0,     0,     0,     0,     0,     0,     0,     0,
       0,     0,     0,    28,     0,   104,     0,     0,     0,     0,
       0,     0,     0,     0,    28,    76,     0,     0,     0,     0,
       0,     0,    32,     0,     0,    61,     0,     0,     0,    72,
      10,    68,    77,    63,    64,    67,    65,    66,    70,    78,
      80,    81,     0,    98,    99,    40,    74,    86,    87,    88,
      92,    91,     0,    30,     0,    93,     0,     0,     0,     0,
       0,     0,    52,     0,    46,     0,     0,    47,    52,    50,
      48,    33,     0,     0,    90,     0,    60,    73,    89,     0,
      83,     0,     0,     0,    95,     0,     0,     0,    37,    53,
       0,     0,    56,     0,     0,    32,    75,     0,    59,    62,
      96,     0,    85,     0,    25,    26,    51,     0,     0,    52,
      44,     0,     0,    57,     0,     0,    42,    34,    31,     0,
       0,    38,    41,    54,     0,     0,    56,    43,    49,    94,
       0,     0,    55,    58,    71,    45
};

/* YYPGOTO[NTERM-NUM].  */
static const yytype_int16 yypgoto[] =
{
    -216,  -216,  -216,  -216,   272,  -216,  -216,   215,  -216,  -216,
    -216,   -66,  -216,  -216,   -96,  -112,  -216,    40,  -216,  -216,
    -216,  -179,  -215,  -216,    13,  -216,    65,   194,  -134,  -143,
    -104,  -216,  -206,   -18,  -216,   255,  -216,   -35,  -216,   228,
    -216,   239
};

/* YYDEFGOTO[NTERM-NUM].  */
static const yytype_int16 yydefgoto[] =
{
       0,     2,     3,     9,    17,     6,    14,    10,    21,    15,
      52,    53,    83,    91,   137,   138,   231,   232,    75,   268,
     167,   249,   250,   273,   274,   185,   186,   123,   124,   125,
     126,   127,   128,    47,    38,    39,    40,    48,    61,    62,
      58,    59
};

/* YYTABLE[YYPACT[STATE-NUM]] -- What to do in state STATE-NUM.  If
   positive, shift that token.  If negative, reduce the rule whose
   number is the opposite.  If YYTABLE_NINF, syntax error.  */
static const yytype_int16 yytable[] =
{
     122,   129,    81,   233,    -2,    37,   153,   150,    42,    56,
     192,   244,    43,   254,    96,   143,   161,   199,   191,    13,
     193,   194,   195,   196,   197,     4,    19,     1,    78,    97,
      20,     5,   159,   260,     7,   168,   169,   170,   171,   172,
     173,   247,   162,   176,   177,   203,   204,    79,   160,    80,
     183,   202,   187,    85,   283,    93,    87,   200,   201,    97,
       8,    13,   213,   107,    89,    11,    92,    16,    12,    18,
     205,    22,   271,    23,   275,   178,   233,    99,   100,   101,
     117,   102,   103,   104,   218,   219,    24,    41,   281,   106,
     120,   121,    44,   107,   108,    45,   110,    46,    49,    50,
      54,    51,    55,   114,    57,   291,   292,   116,    60,    63,
     117,    64,   118,    65,    68,    67,   241,    69,   242,    70,
     120,   121,    71,    72,   179,    76,    73,    74,    77,    82,
      84,   188,    90,    94,    97,   130,   131,   132,   133,   258,
     134,   198,   135,   136,   139,    98,   140,   141,   142,   264,
     265,   144,    99,   100,   101,   146,   102,   103,   104,   147,
     105,   278,   148,   163,   106,   279,   151,   280,   107,   108,
     109,   110,   111,   164,   149,   165,   112,   113,   114,   174,
     115,    97,   116,   166,   175,   117,   182,   118,   180,   181,
     119,   189,    98,   184,   207,   120,   121,   208,   206,    99,
     100,   101,   209,   102,   103,   104,   210,   105,   190,   211,
     220,   106,   215,   212,   216,   107,   108,   109,   110,   214,
     234,   221,   217,   237,   113,   114,   235,   115,    26,   116,
     236,   238,   117,   239,   118,   240,   222,   119,   243,   245,
     223,   246,   120,   121,   224,    27,   248,   251,   252,    28,
     253,   255,    26,    29,    30,   256,   225,   261,   226,   257,
     262,   227,   266,   263,    31,   270,   228,   267,   269,    27,
     276,   229,   230,    28,    32,   284,   286,    29,    30,   272,
     282,   285,    33,   287,    34,   288,   152,    35,   290,    36,
     153,   289,   295,   294,    25,   277,   154,   155,    32,   293,
     156,   259,   157,   158,    88,    66,    33,   145,    34,    95,
       0,    86,     0,    36,     0,     0,   159,     0,     0,     0,
       0,     0,     0,     0,     0,     0,     0,     0,     0,     0,
       0,     0,   160
};

static const yytype_int16 yycheck[] =
{
      96,    97,    68,   182,     0,    23,     8,   119,    26,    44,
     153,   217,    30,   228,    52,   111,     7,   160,   152,    57,
     154,   155,   156,   157,   158,    36,    41,    46,    63,     5,
      45,     0,    34,   239,    13,   131,   132,   133,   134,   135,
     136,   220,    33,   139,   140,    66,    67,    65,    50,    67,
     146,   163,   148,    71,   269,    90,    74,   161,   162,     5,
      38,    57,   174,    39,    82,    60,    84,    65,    13,    66,
     166,     9,   251,    17,   253,   141,   255,    23,    24,    25,
      56,    27,    28,    29,   180,   181,    66,     5,   267,    35,
      66,    67,     5,    39,    40,    61,    42,    16,    66,     8,
       6,    66,    32,    49,    66,   284,   285,    53,    66,     9,
      56,    63,    58,    11,     9,    12,   212,     6,   214,     6,
      66,    67,    12,     9,   142,     9,    63,    12,    62,    10,
      10,   149,    55,    61,     5,    66,     5,     5,     5,   235,
       5,   159,     5,     5,     5,    16,     5,     5,    31,   245,
     246,    66,    23,    24,    25,     5,    27,    28,    29,    61,
      31,   257,     5,     5,    35,   261,    13,   263,    39,    40,
      41,    42,    43,    11,    31,     6,    47,    48,    49,     9,
      51,     5,    53,    17,    32,    56,    61,    58,    54,    17,
      61,    63,    16,    66,     6,    66,    67,     6,    62,    23,
      24,    25,     6,    27,    28,    29,     6,    31,    63,     6,
       5,    35,     6,     9,     6,    39,    40,    41,    42,     9,
       6,    16,    32,    63,    48,    49,    17,    51,     5,    53,
       9,     6,    56,    32,    58,     6,    31,    61,    61,    37,
      35,    44,    66,    67,    39,    22,    66,     5,    61,    26,
       5,    13,     5,    30,    31,    63,    51,     9,    53,    19,
       6,    56,     6,    52,    41,    32,    61,    17,     9,    22,
      63,    66,    67,    26,    51,     9,     9,    30,    31,    66,
      62,    17,    59,    63,    61,     6,     4,    64,    13,    66,
       8,     6,     6,    63,    22,   255,    14,    15,    51,   286,
      18,   236,    20,    21,    76,    50,    59,   113,    61,    94,
      -1,    72,    -1,    66,    -1,    -1,    34,    -1,    -1,    -1,
      -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,
      -1,    -1,    50
};

/* YYSTOS[STATE-NUM] -- The symbol kind of the accessing symbol of
   state STATE-NUM.  */
static const yytype_int8 yystos[] =
{
       0,    46,    69,    70,    36,     0,    73,    13,    38,    71,
      75,    60,    13,    57,    74,    77,    65,    72,    66,    41,
      45,    76,     9,    17,    66,    72,     5,    22,    26,    30,
      31,    41,    51,    59,    61,    64,    66,   101,   102,   103,
     104,     5,   101,   101,     5,    61,    16,   101,   105,    66,
       8,    66,    78,    79,     6,    32,   105,    66,   108,   109,
      66,   106,   107,     9,    63,    11,   103,    12,     9,     6,
       6,    12,     9,    63,    12,    86,     9,    62,   105,   101,
     101,    79,    10,    80,    10,   101,   109,   101,   107,   101,
      55,    81,   101,   105,    61,    75,    52,     5,    16,    23,
      24,    25,    27,    28,    29,    31,    35,    39,    40,    41,
      42,    43,    47,    48,    49,    51,    53,    56,    58,    61,
      66,    67,    82,    95,    96,    97,    98,    99,   100,    82,
      66,     5,     5,     5,     5,     5,     5,    82,    83,     5,
       5,     5,    31,    82,    66,    95,     5,    61,     5,    31,
      83,    13,     4,     8,    14,    15,    18,    20,    21,    34,
      50,     7,    33,     5,    11,     6,    17,    88,    82,    82,
      82,    82,    82,    82,     9,    32,    82,    82,    79,   101,
      54,    17,    61,    82,    66,    93,    94,    82,   101,    63,
      63,    96,    97,    96,    96,    96,    96,    96,   101,    97,
      98,    98,    83,    66,    67,    82,    62,     6,     6,     6,
       6,     6,     9,    83,     9,     6,     6,    32,    82,    82,
       5,    16,    31,    35,    39,    51,    53,    56,    61,    66,
      67,    84,    85,    89,     6,    17,     9,    63,     6,    32,
       6,    82,    82,    61,   100,    37,    44,    89,    66,    89,
      90,     5,    61,     5,    90,    13,    63,    19,    82,    94,
     100,     9,     6,    52,    82,    82,     6,    17,    87,     9,
      32,    89,    66,    91,    92,    89,    63,    85,    82,    82,
      82,    89,    62,    90,     9,    17,     9,    63,     6,     6,
      13,    89,    89,    92,    63,     6
};

/* YYR1[RULE-NUM] -- Symbol kind of the left-hand side of rule RULE-NUM.  */
static const yytype_int8 yyr1[] =
{
       0,    68,    69,    70,    71,    72,    72,    72,    73,    73,
      74,    74,    75,    75,    76,    77,    77,    78,    79,    79,
      79,    80,    80,    81,    81,    82,    82,    82,    83,    83,
      83,    84,    85,    85,    85,    86,    86,    87,    87,    88,
      88,    89,    89,    89,    89,    89,    89,    89,    89,    89,
      89,    89,    90,    90,    90,    91,    92,    92,    92,    93,
      94,    94,    94,    95,    95,    95,    95,    95,    95,    95,
      96,    96,    96,    96,    96,    96,    96,    96,    96,    96,
      97,    97,    97,    98,    98,    99,    99,    99,    99,    99,
      99,    99,    99,    99,    99,    99,    99,    99,   100,   100,
     100,   100,   100,   100,   100,   101,   101,   101,   102,   102,
     103,   103,   103,   103,   103,   104,   104,   104,   104,   104,
     105,   105,   105,   106,   107,   107,   107,   108,   109,   109,
     109
};

/* YYR2[RULE-NUM] -- Number of symbols on the right-hand side of rule RULE-NUM.  */
static const yytype_int8 yyr2[] =
{
       0,     2,     3,     3,     3,     0,     1,     3,     0,     3,
      14,     4,     0,     2,     1,     0,     2,     3,     0,     1,
       3,     0,     2,     0,     2,     6,     6,     1,     0,     1,
       3,     3,     0,     1,     3,     0,     2,     0,     2,     0,
       2,     4,     3,     4,     3,     6,     1,     1,     1,     4,
       1,     3,     0,     1,     3,     3,     0,     1,     3,     3,
       0,     1,     3,     3,     3,     3,     3,     3,     3,     1,
       3,     9,     3,     4,     4,     5,     3,     3,     3,     1,
       3,     3,     1,     4,     1,     6,     4,     4,     4,     4,
       4,     4,     4,     4,     8,     5,     5,     1,     3,     3,
       1,     1,     1,     1,     3,     6,     4,     1,     3,     1,
       3,     4,     4,     3,     1,     1,     1,     1,     1,     3,
       0,     1,     3,     2,     0,     1,     3,     3,     0,     1,
       3
};


enum { YYENOMEM = -2 };

#define yyerrok         (yyerrstatus = 0)
#define yyclearin       (yychar = YYEMPTY)

#define YYACCEPT        goto yyacceptlab
#define YYABORT         goto yyabortlab
#define YYERROR         goto yyerrorlab
#define YYNOMEM         goto yyexhaustedlab


#define YYRECOVERING()  (!!yyerrstatus)

#define YYBACKUP(Token, Value)                                    \
  do                                                              \
    if (yychar == YYEMPTY)                                        \
      {                                                           \
        yychar = (Token);                                         \
        yylval = (Value);                                         \
        YYPOPSTACK (yylen);                                       \
        yystate = *yyssp;                                         \
        goto yybackup;                                            \
      }                                                           \
    else                                                          \
      {                                                           \
        yyerror (&yylloc, scanner, result, YY_("syntax error: cannot back up")); \
        YYERROR;                                                  \
      }                                                           \
  while (0)

/* Backward compatibility with an undocumented macro.
   Use YYerror or YYUNDEF. */
#define YYERRCODE YYUNDEF

/* YYLLOC_DEFAULT -- Set CURRENT to span from RHS[1] to RHS[N].
   If N is 0, then set CURRENT to the empty location which ends
   the previous symbol: RHS[0] (always defined).  */

#ifndef YYLLOC_DEFAULT
# define YYLLOC_DEFAULT(Current, Rhs, N)                                \
    do                                                                  \
      if (N)                                                            \
        {                                                               \
          (Current).first_line   = YYRHSLOC (Rhs, 1).first_line;        \
          (Current).first_column = YYRHSLOC (Rhs, 1).first_column;      \
          (Current).last_line    = YYRHSLOC (Rhs, N).last_line;         \
          (Current).last_column  = YYRHSLOC (Rhs, N).last_column;       \
        }                                                               \
      else                                                              \
        {                                                               \
          (Current).first_line   = (Current).last_line   =              \
            YYRHSLOC (Rhs, 0).last_line;                                \
          (Current).first_column = (Current).last_column =              \
            YYRHSLOC (Rhs, 0).last_column;                              \
        }                                                               \
    while (0)
#endif

#define YYRHSLOC(Rhs, K) ((Rhs)[K])


/* Enable debugging if requested.  */
#if YYDEBUG

# ifndef YYFPRINTF
#  include <stdio.h> /* INFRINGES ON USER NAME SPACE */
#  define YYFPRINTF fprintf
# endif

# define YYDPRINTF(Args)                        \
do {                                            \
  if (yydebug)                                  \
    YYFPRINTF Args;                             \
} while (0)


/* YYLOCATION_PRINT -- Print the location on the stream.
   This macro was not mandated originally: define only if we know
   we won't break user code: when these are the locations we know.  */

# ifndef YYLOCATION_PRINT

#  if defined YY_LOCATION_PRINT

   /* Temporary convenience wrapper in case some people defined the
      undocumented and private YY_LOCATION_PRINT macros.  */
#   define YYLOCATION_PRINT(File, Loc)  YY_LOCATION_PRINT(File, *(Loc))

#  elif defined YYLTYPE_IS_TRIVIAL && YYLTYPE_IS_TRIVIAL

/* Print *YYLOCP on YYO.  Private, do not rely on its existence. */

YY_ATTRIBUTE_UNUSED
static int
yy_location_print_ (FILE *yyo, YYLTYPE const * const yylocp)
{
  int res = 0;
  int end_col = 0 != yylocp->last_column ? yylocp->last_column - 1 : 0;
  if (0 <= yylocp->first_line)
    {
      res += YYFPRINTF (yyo, "%d", yylocp->first_line);
      if (0 <= yylocp->first_column)
        res += YYFPRINTF (yyo, ".%d", yylocp->first_column);
    }
  if (0 <= yylocp->last_line)
    {
      if (yylocp->first_line < yylocp->last_line)
        {
          res += YYFPRINTF (yyo, "-%d", yylocp->last_line);
          if (0 <= end_col)
            res += YYFPRINTF (yyo, ".%d", end_col);
        }
      else if (0 <= end_col && yylocp->first_column < end_col)
        res += YYFPRINTF (yyo, "-%d", end_col);
    }
  return res;
}

#   define YYLOCATION_PRINT  yy_location_print_

    /* Temporary convenience wrapper in case some people defined the
       undocumented and private YY_LOCATION_PRINT macros.  */
#   define YY_LOCATION_PRINT(File, Loc)  YYLOCATION_PRINT(File, &(Loc))

#  else

#   define YYLOCATION_PRINT(File, Loc) ((void) 0)
    /* Temporary convenience wrapper in case some people defined the
       undocumented and private YY_LOCATION_PRINT macros.  */
#   define YY_LOCATION_PRINT  YYLOCATION_PRINT

#  endif
# endif /* !defined YYLOCATION_PRINT */


# define YY_SYMBOL_PRINT(Title, Kind, Value, Location)                    \
do {                                                                      \
  if (yydebug)                                                            \
    {                                                                     \
      YYFPRINTF (stderr, "%s ", Title);                                   \
      yy_symbol_print (stderr,                                            \
                  Kind, Value, Location, scanner, result); \
      YYFPRINTF (stderr, "\n");                                           \
    }                                                                     \
} while (0)


/*-----------------------------------.
| Print this symbol's value on YYO.  |
`-----------------------------------*/

static void
yy_symbol_value_print (FILE *yyo,
                       yysymbol_kind_t yykind, YYSTYPE const * const yyvaluep, YYLTYPE const * const yylocationp, yyscan_t scanner, YYSTYPE *result)
{
  FILE *yyoutput = yyo;
  YY_USE (yyoutput);
  YY_USE (yylocationp);
  YY_USE (scanner);
  YY_USE (result);
  if (!yyvaluep)
    return;
  YY_IGNORE_MAYBE_UNINITIALIZED_BEGIN
  YY_USE (yykind);
  YY_IGNORE_MAYBE_UNINITIALIZED_END
}


/*---------------------------.
| Print this symbol on YYO.  |
`---------------------------*/

static void
yy_symbol_print (FILE *yyo,
                 yysymbol_kind_t yykind, YYSTYPE const * const yyvaluep, YYLTYPE const * const yylocationp, yyscan_t scanner, YYSTYPE *result)
{
  YYFPRINTF (yyo, "%s %s (",
             yykind < YYNTOKENS ? "token" : "nterm", yysymbol_name (yykind));

  YYLOCATION_PRINT (yyo, yylocationp);
  YYFPRINTF (yyo, ": ");
  yy_symbol_value_print (yyo, yykind, yyvaluep, yylocationp, scanner, result);
  YYFPRINTF (yyo, ")");
}

/*------------------------------------------------------------------.
| yy_stack_print -- Print the state stack from its BOTTOM up to its |
| TOP (included).                                                   |
`------------------------------------------------------------------*/

static void
yy_stack_print (yy_state_t *yybottom, yy_state_t *yytop)
{
  YYFPRINTF (stderr, "Stack now");
  for (; yybottom <= yytop; yybottom++)
    {
      int yybot = *yybottom;
      YYFPRINTF (stderr, " %d", yybot);
    }
  YYFPRINTF (stderr, "\n");
}

# define YY_STACK_PRINT(Bottom, Top)                            \
do {                                                            \
  if (yydebug)                                                  \
    yy_stack_print ((Bottom), (Top));                           \
} while (0)


/*------------------------------------------------.
| Report that the YYRULE is going to be reduced.  |
`------------------------------------------------*/

static void
yy_reduce_print (yy_state_t *yyssp, YYSTYPE *yyvsp, YYLTYPE *yylsp,
                 int yyrule, yyscan_t scanner, YYSTYPE *result)
{
  int yylno = yyrline[yyrule];
  int yynrhs = yyr2[yyrule];
  int yyi;
  YYFPRINTF (stderr, "Reducing stack by rule %d (line %d):\n",
             yyrule - 1, yylno);
  /* The symbols being reduced.  */
  for (yyi = 0; yyi < yynrhs; yyi++)
    {
      YYFPRINTF (stderr, "   $%d = ", yyi + 1);
      yy_symbol_print (stderr,
                       YY_ACCESSING_SYMBOL (+yyssp[yyi + 1 - yynrhs]),
                       &yyvsp[(yyi + 1) - (yynrhs)],
                       &(yylsp[(yyi + 1) - (yynrhs)]), scanner, result);
      YYFPRINTF (stderr, "\n");
    }
}

# define YY_REDUCE_PRINT(Rule)          \
do {                                    \
  if (yydebug)                          \
    yy_reduce_print (yyssp, yyvsp, yylsp, Rule, scanner, result); \
} while (0)

/* Nonzero means print parse trace.  It is left uninitialized so that
   multiple parsers can coexist.  */
int yydebug;
#else /* !YYDEBUG */
# define YYDPRINTF(Args) ((void) 0)
# define YY_SYMBOL_PRINT(Title, Kind, Value, Location)
# define YY_STACK_PRINT(Bottom, Top)
# define YY_REDUCE_PRINT(Rule)
#endif /* !YYDEBUG */


/* YYINITDEPTH -- initial size of the parser's stacks.  */
#ifndef YYINITDEPTH
# define YYINITDEPTH 200
#endif

/* YYMAXDEPTH -- maximum size the stacks can grow to (effective only
   if the built-in stack extension method is used).

   Do not make this value too large; the results are undefined if
   YYSTACK_ALLOC_MAXIMUM < YYSTACK_BYTES (YYMAXDEPTH)
   evaluated with infinite-precision integer arithmetic.  */

#ifndef YYMAXDEPTH
# define YYMAXDEPTH 10000
#endif






/*-----------------------------------------------.
| Release the memory associated to this symbol.  |
`-----------------------------------------------*/

static void
yydestruct (const char *yymsg,
            yysymbol_kind_t yykind, YYSTYPE *yyvaluep, YYLTYPE *yylocationp, yyscan_t scanner, YYSTYPE *result)
{
  YY_USE (yyvaluep);
  YY_USE (yylocationp);
  YY_USE (scanner);
  YY_USE (result);
  if (!yymsg)
    yymsg = "Deleting";
  YY_SYMBOL_PRINT (yymsg, yykind, yyvaluep, yylocationp);

  YY_IGNORE_MAYBE_UNINITIALIZED_BEGIN
  YY_USE (yykind);
  YY_IGNORE_MAYBE_UNINITIALIZED_END
}






/*----------.
| yyparse.  |
`----------*/

int
yyparse (yyscan_t scanner, YYSTYPE *result)
{
/* Lookahead token kind.  */
int yychar;


/* The semantic value of the lookahead symbol.  */
/* Default value used for initialization, for pacifying older GCCs
   or non-GCC compilers.  */
YY_INITIAL_VALUE (static YYSTYPE yyval_default;)
YYSTYPE yylval YY_INITIAL_VALUE (= yyval_default);

/* Location data for the lookahead symbol.  */
static YYLTYPE yyloc_default
# if defined YYLTYPE_IS_TRIVIAL && YYLTYPE_IS_TRIVIAL
  = { 1, 1, 1, 1 }
# endif
;
YYLTYPE yylloc = yyloc_default;

    /* Number of syntax errors so far.  */
    int yynerrs = 0;

    yy_state_fast_t yystate = 0;
    /* Number of tokens to shift before error messages enabled.  */
    int yyerrstatus = 0;

    /* Refer to the stacks through separate pointers, to allow yyoverflow
       to reallocate them elsewhere.  */

    /* Their size.  */
    YYPTRDIFF_T yystacksize = YYINITDEPTH;

    /* The state stack: array, bottom, top.  */
    yy_state_t yyssa[YYINITDEPTH];
    yy_state_t *yyss = yyssa;
    yy_state_t *yyssp = yyss;

    /* The semantic value stack: array, bottom, top.  */
    YYSTYPE yyvsa[YYINITDEPTH];
    YYSTYPE *yyvs = yyvsa;
    YYSTYPE *yyvsp = yyvs;

    /* The location stack: array, bottom, top.  */
    YYLTYPE yylsa[YYINITDEPTH];
    YYLTYPE *yyls = yylsa;
    YYLTYPE *yylsp = yyls;

  int yyn;
  /* The return value of yyparse.  */
  int yyresult;
  /* Lookahead symbol kind.  */
  yysymbol_kind_t yytoken = YYSYMBOL_YYEMPTY;
  /* The variables used to return semantic value and location from the
     action routines.  */
  YYSTYPE yyval;
  YYLTYPE yyloc;

  /* The locations where the error started and ended.  */
  YYLTYPE yyerror_range[3];



#define YYPOPSTACK(N)   (yyvsp -= (N), yyssp -= (N), yylsp -= (N))

  /* The number of symbols on the RHS of the reduced rule.
     Keep to zero when no symbol should be popped.  */
  int yylen = 0;

  YYDPRINTF ((stderr, "Starting parse\n"));

  yychar = YYEMPTY; /* Cause a token to be read.  */

  yylsp[0] = yylloc;
  goto yysetstate;


/*------------------------------------------------------------.
| yynewstate -- push a new state, which is found in yystate.  |
`------------------------------------------------------------*/
yynewstate:
  /* In all cases, when you get here, the value and location stacks
     have just been pushed.  So pushing a state here evens the stacks.  */
  yyssp++;


/*--------------------------------------------------------------------.
| yysetstate -- set current state (the top of the stack) to yystate.  |
`--------------------------------------------------------------------*/
yysetstate:
  YYDPRINTF ((stderr, "Entering state %d\n", yystate));
  YY_ASSERT (0 <= yystate && yystate < YYNSTATES);
  YY_IGNORE_USELESS_CAST_BEGIN
  *yyssp = YY_CAST (yy_state_t, yystate);
  YY_IGNORE_USELESS_CAST_END
  YY_STACK_PRINT (yyss, yyssp);

  if (yyss + yystacksize - 1 <= yyssp)
#if !defined yyoverflow && !defined YYSTACK_RELOCATE
    YYNOMEM;
#else
    {
      /* Get the current used size of the three stacks, in elements.  */
      YYPTRDIFF_T yysize = yyssp - yyss + 1;

# if defined yyoverflow
      {
        /* Give user a chance to reallocate the stack.  Use copies of
           these so that the &'s don't force the real ones into
           memory.  */
        yy_state_t *yyss1 = yyss;
        YYSTYPE *yyvs1 = yyvs;
        YYLTYPE *yyls1 = yyls;

        /* Each stack pointer address is followed by the size of the
           data in use in that stack, in bytes.  This used to be a
           conditional around just the two extra args, but that might
           be undefined if yyoverflow is a macro.  */
        yyoverflow (YY_("memory exhausted"),
                    &yyss1, yysize * YYSIZEOF (*yyssp),
                    &yyvs1, yysize * YYSIZEOF (*yyvsp),
                    &yyls1, yysize * YYSIZEOF (*yylsp),
                    &yystacksize);
        yyss = yyss1;
        yyvs = yyvs1;
        yyls = yyls1;
      }
# else /* defined YYSTACK_RELOCATE */
      /* Extend the stack our own way.  */
      if (YYMAXDEPTH <= yystacksize)
        YYNOMEM;
      yystacksize *= 2;
      if (YYMAXDEPTH < yystacksize)
        yystacksize = YYMAXDEPTH;

      {
        yy_state_t *yyss1 = yyss;
        union yyalloc *yyptr =
          YY_CAST (union yyalloc *,
                   YYSTACK_ALLOC (YY_CAST (YYSIZE_T, YYSTACK_BYTES (yystacksize))));
        if (! yyptr)
          YYNOMEM;
        YYSTACK_RELOCATE (yyss_alloc, yyss);
        YYSTACK_RELOCATE (yyvs_alloc, yyvs);
        YYSTACK_RELOCATE (yyls_alloc, yyls);
#  undef YYSTACK_RELOCATE
        if (yyss1 != yyssa)
          YYSTACK_FREE (yyss1);
      }
# endif

      yyssp = yyss + yysize - 1;
      yyvsp = yyvs + yysize - 1;
      yylsp = yyls + yysize - 1;

      YY_IGNORE_USELESS_CAST_BEGIN
      YYDPRINTF ((stderr, "Stack size increased to %ld\n",
                  YY_CAST (long, yystacksize)));
      YY_IGNORE_USELESS_CAST_END

      if (yyss + yystacksize - 1 <= yyssp)
        YYABORT;
    }
#endif /* !defined yyoverflow && !defined YYSTACK_RELOCATE */


  if (yystate == YYFINAL)
    YYACCEPT;

  goto yybackup;


/*-----------.
| yybackup.  |
`-----------*/
yybackup:
  /* Do appropriate processing given the current state.  Read a
     lookahead token if we need one and don't already have one.  */

  /* First try to decide what to do without reference to lookahead token.  */
  yyn = yypact[yystate];
  if (yypact_value_is_default (yyn))
    goto yydefault;

  /* Not known => get a lookahead token if don't already have one.  */

  /* YYCHAR is either empty, or end-of-input, or a valid lookahead.  */
  if (yychar == YYEMPTY)
    {
      YYDPRINTF ((stderr, "Reading a token\n"));
      yychar = yylex (&yylval, &yylloc, scanner);
    }

  if (yychar <= YYEOF)
    {
      yychar = YYEOF;
      yytoken = YYSYMBOL_YYEOF;
      YYDPRINTF ((stderr, "Now at end of input.\n"));
    }
  else if (yychar == YYerror)
    {
      /* The scanner already issued an error message, process directly
         to error recovery.  But do not keep the error token as
         lookahead, it is too special and may lead us to an endless
         loop in error recovery. */
      yychar = YYUNDEF;
      yytoken = YYSYMBOL_YYerror;
      yyerror_range[1] = yylloc;
      goto yyerrlab1;
    }
  else
    {
      yytoken = YYTRANSLATE (yychar);
      YY_SYMBOL_PRINT ("Next token is", yytoken, &yylval, &yylloc);
    }

  /* If the proper action on seeing token YYTOKEN is to reduce or to
     detect an error, take that action.  */
  yyn += yytoken;
  if (yyn < 0 || YYLAST < yyn || yycheck[yyn] != yytoken)
    goto yydefault;
  yyn = yytable[yyn];
  if (yyn <= 0)
    {
      if (yytable_value_is_error (yyn))
        goto yyerrlab;
      yyn = -yyn;
      goto yyreduce;
    }

  /* Count tokens shifted since error; after three, turn off error
     status.  */
  if (yyerrstatus)
    yyerrstatus--;

  /* Shift the lookahead token.  */
  YY_SYMBOL_PRINT ("Shifting", yytoken, &yylval, &yylloc);
  yystate = yyn;
  YY_IGNORE_MAYBE_UNINITIALIZED_BEGIN
  *++yyvsp = yylval;
  YY_IGNORE_MAYBE_UNINITIALIZED_END
  *++yylsp = yylloc;

  /* Discard the shifted token.  */
  yychar = YYEMPTY;
  goto yynewstate;


/*-----------------------------------------------------------.
| yydefault -- do the default action for the current state.  |
`-----------------------------------------------------------*/
yydefault:
  yyn = yydefact[yystate];
  if (yyn == 0)
    goto yyerrlab;
  goto yyreduce;


/*-----------------------------.
| yyreduce -- do a reduction.  |
`-----------------------------*/
yyreduce:
  /* yyn is the number of a rule to reduce with.  */
  yylen = yyr2[yyn];

  /* If YYLEN is nonzero, implement the default value of the action:
     '$$ = $1'.

     Otherwise, the following line sets YYVAL to garbage.
     This behavior is undocumented and Bison
     users should not rely upon it.  Assigning to YYVAL
     unconditionally makes the parser a bit smaller, and it avoids a
     GCC warning that YYVAL may be used uninitialized.  */
  yyval = yyvsp[1-yylen];

  /* Default location. */
  YYLLOC_DEFAULT (yyloc, (yylsp - yylen), yylen);
  yyerror_range[1] = yyloc;
  YY_REDUCE_PRINT (yyn);
  switch (yyn)
    {
  case 2: /* Program: LanguageDecl ListExtension ListDecl  */
#line 223 "Stella.y"
                                              { (yyval.program_) = new Stella::AProgram((yyvsp[-2].languagedecl_), (yyvsp[-1].listextension_), (yyvsp[0].listdecl_)); (yyval.program_)->line_number = (yyloc).first_line; (yyval.program_)->char_number = (yyloc).first_column; result->program_ = (yyval.program_); }
#line 1555 "Parser.C"
    break;

  case 3: /* LanguageDecl: _KW_language _KW_core _SEMI  */
#line 229 "Stella.y"
                                           { (yyval.languagedecl_) = new Stella::LanguageCore(); (yyval.languagedecl_)->line_number = (yyloc).first_line; (yyval.languagedecl_)->char_number = (yyloc).first_column; result->languagedecl_ = (yyval.languagedecl_); }
#line 1561 "Parser.C"
    break;

  case 4: /* Extension: _KW_extend _KW_with ListExtensionName  */
#line 231 "Stella.y"
                                                  { std::reverse((yyvsp[0].listextensionname_)->begin(),(yyvsp[0].listextensionname_)->end()) ;(yyval.extension_) = new Stella::AnExtension((yyvsp[0].listextensionname_)); (yyval.extension_)->line_number = (yyloc).first_line; (yyval.extension_)->char_number = (yyloc).first_column; result->extension_ = (yyval.extension_); }
#line 1567 "Parser.C"
    break;

  case 5: /* ListExtensionName: %empty  */
#line 233 "Stella.y"
                                { (yyval.listextensionname_) = new Stella::ListExtensionName(); result->listextensionname_ = (yyval.listextensionname_); }
#line 1573 "Parser.C"
    break;

  case 6: /* ListExtensionName: T_ExtensionName  */
#line 234 "Stella.y"
                    { (yyval.listextensionname_) = new Stella::ListExtensionName(); (yyval.listextensionname_)->push_back((yyvsp[0]._string)); result->listextensionname_ = (yyval.listextensionname_); }
#line 1579 "Parser.C"
    break;

  case 7: /* ListExtensionName: T_ExtensionName _COMMA ListExtensionName  */
#line 235 "Stella.y"
                                             { (yyvsp[0].listextensionname_)->push_back((yyvsp[-2]._string)); (yyval.listextensionname_) = (yyvsp[0].listextensionname_); result->listextensionname_ = (yyval.listextensionname_); }
#line 1585 "Parser.C"
    break;

  case 8: /* ListExtension: %empty  */
#line 237 "Stella.y"
                            { (yyval.listextension_) = new Stella::ListExtension(); result->listextension_ = (yyval.listextension_); }
#line 1591 "Parser.C"
    break;

  case 9: /* ListExtension: ListExtension Extension _SEMI  */
#line 238 "Stella.y"
                                  { (yyvsp[-2].listextension_)->push_back((yyvsp[-1].extension_)); (yyval.listextension_) = (yyvsp[-2].listextension_); result->listextension_ = (yyval.listextension_); }
#line 1597 "Parser.C"
    break;

  case 10: /* Decl: ListAnnotation _KW_fn T_StellaIdent _LPAREN ListParamDecl _RPAREN ReturnType ThrowType _LBRACE ListDecl _KW_return Expr _SEMI _RBRACE  */
#line 240 "Stella.y"
                                                                                                                                             { std::reverse((yyvsp[-9].listparamdecl_)->begin(),(yyvsp[-9].listparamdecl_)->end()) ;(yyval.decl_) = new Stella::DeclFun((yyvsp[-13].listannotation_), (yyvsp[-11]._string), (yyvsp[-9].listparamdecl_), (yyvsp[-7].returntype_), (yyvsp[-6].throwtype_), (yyvsp[-4].listdecl_), (yyvsp[-2].expr_)); (yyval.decl_)->line_number = (yyloc).first_line; (yyval.decl_)->char_number = (yyloc).first_column; result->decl_ = (yyval.decl_); }
#line 1603 "Parser.C"
    break;

  case 11: /* Decl: _KW_type T_StellaIdent _EQ Type  */
#line 241 "Stella.y"
                                    { (yyval.decl_) = new Stella::DeclTypeAlias((yyvsp[-2]._string), (yyvsp[0].type_)); (yyval.decl_)->line_number = (yyloc).first_line; (yyval.decl_)->char_number = (yyloc).first_column; result->decl_ = (yyval.decl_); }
#line 1609 "Parser.C"
    break;

  case 12: /* ListDecl: %empty  */
#line 243 "Stella.y"
                       { (yyval.listdecl_) = new Stella::ListDecl(); result->listdecl_ = (yyval.listdecl_); }
#line 1615 "Parser.C"
    break;

  case 13: /* ListDecl: ListDecl Decl  */
#line 244 "Stella.y"
                  { (yyvsp[-1].listdecl_)->push_back((yyvsp[0].decl_)); (yyval.listdecl_) = (yyvsp[-1].listdecl_); result->listdecl_ = (yyval.listdecl_); }
#line 1621 "Parser.C"
    break;

  case 14: /* Annotation: _KW_inline  */
#line 251 "Stella.y"
                        { (yyval.annotation_) = new Stella::InlineAnnotation(); (yyval.annotation_)->line_number = (yyloc).first_line; (yyval.annotation_)->char_number = (yyloc).first_column; result->annotation_ = (yyval.annotation_); }
#line 1627 "Parser.C"
    break;

  case 15: /* ListAnnotation: %empty  */
#line 253 "Stella.y"
                             { (yyval.listannotation_) = new Stella::ListAnnotation(); result->listannotation_ = (yyval.listannotation_); }
#line 1633 "Parser.C"
    break;

  case 16: /* ListAnnotation: ListAnnotation Annotation  */
#line 254 "Stella.y"
                              { (yyvsp[-1].listannotation_)->push_back((yyvsp[0].annotation_)); (yyval.listannotation_) = (yyvsp[-1].listannotation_); result->listannotation_ = (yyval.listannotation_); }
#line 1639 "Parser.C"
    break;

  case 17: /* ParamDecl: T_StellaIdent _COLON Type  */
#line 256 "Stella.y"
                                      { (yyval.paramdecl_) = new Stella::AParamDecl((yyvsp[-2]._string), (yyvsp[0].type_)); (yyval.paramdecl_)->line_number = (yyloc).first_line; (yyval.paramdecl_)->char_number = (yyloc).first_column; result->paramdecl_ = (yyval.paramdecl_); }
#line 1645 "Parser.C"
    break;

  case 18: /* ListParamDecl: %empty  */
#line 258 "Stella.y"
                            { (yyval.listparamdecl_) = new Stella::ListParamDecl(); result->listparamdecl_ = (yyval.listparamdecl_); }
#line 1651 "Parser.C"
    break;

  case 19: /* ListParamDecl: ParamDecl  */
#line 259 "Stella.y"
              { (yyval.listparamdecl_) = new Stella::ListParamDecl(); (yyval.listparamdecl_)->push_back((yyvsp[0].paramdecl_)); result->listparamdecl_ = (yyval.listparamdecl_); }
#line 1657 "Parser.C"
    break;

  case 20: /* ListParamDecl: ParamDecl _COMMA ListParamDecl  */
#line 260 "Stella.y"
                                   { (yyvsp[0].listparamdecl_)->push_back((yyvsp[-2].paramdecl_)); (yyval.listparamdecl_) = (yyvsp[0].listparamdecl_); result->listparamdecl_ = (yyval.listparamdecl_); }
#line 1663 "Parser.C"
    break;

  case 21: /* ReturnType: %empty  */
#line 262 "Stella.y"
                         { (yyval.returntype_) = new Stella::NoReturnType(); (yyval.returntype_)->line_number = (yyloc).first_line; (yyval.returntype_)->char_number = (yyloc).first_column; result->returntype_ = (yyval.returntype_); }
#line 1669 "Parser.C"
    break;

  case 22: /* ReturnType: _RARROW Type  */
#line 263 "Stella.y"
                 { (yyval.returntype_) = new Stella::SomeReturnType((yyvsp[0].type_)); (yyval.returntype_)->line_number = (yyloc).first_line; (yyval.returntype_)->char_number = (yyloc).first_column; result->returntype_ = (yyval.returntype_); }
#line 1675 "Parser.C"
    break;

  case 23: /* ThrowType: %empty  */
#line 265 "Stella.y"
                        { (yyval.throwtype_) = new Stella::NoThrowType(); (yyval.throwtype_)->line_number = (yyloc).first_line; (yyval.throwtype_)->char_number = (yyloc).first_column; result->throwtype_ = (yyval.throwtype_); }
#line 1681 "Parser.C"
    break;

  case 24: /* ThrowType: _KW_throws ListType  */
#line 266 "Stella.y"
                        { std::reverse((yyvsp[0].listtype_)->begin(),(yyvsp[0].listtype_)->end()) ;(yyval.throwtype_) = new Stella::SomeThrowType((yyvsp[0].listtype_)); (yyval.throwtype_)->line_number = (yyloc).first_line; (yyval.throwtype_)->char_number = (yyloc).first_column; result->throwtype_ = (yyval.throwtype_); }
#line 1687 "Parser.C"
    break;

  case 25: /* Expr: _KW_if Expr _KW_then Expr _KW_else Expr  */
#line 268 "Stella.y"
                                               { (yyval.expr_) = new Stella::If((yyvsp[-4].expr_), (yyvsp[-2].expr_), (yyvsp[0].expr_)); (yyval.expr_)->line_number = (yyloc).first_line; (yyval.expr_)->char_number = (yyloc).first_column; result->expr_ = (yyval.expr_); }
#line 1693 "Parser.C"
    break;

  case 26: /* Expr: _KW_let T_StellaIdent _EQ Expr _KW_in Expr  */
#line 269 "Stella.y"
                                               { (yyval.expr_) = new Stella::Let((yyvsp[-4]._string), (yyvsp[-2].expr_), (yyvsp[0].expr_)); (yyval.expr_)->line_number = (yyloc).first_line; (yyval.expr_)->char_number = (yyloc).first_column; result->expr_ = (yyval.expr_); }
#line 1699 "Parser.C"
    break;

  case 27: /* Expr: Expr1  */
#line 270 "Stella.y"
          { (yyval.expr_) = (yyvsp[0].expr_); (yyval.expr_)->line_number = (yyloc).first_line; (yyval.expr_)->char_number = (yyloc).first_column; result->expr_ = (yyval.expr_); }
#line 1705 "Parser.C"
    break;

  case 28: /* ListExpr: %empty  */
#line 272 "Stella.y"
                       { (yyval.listexpr_) = new Stella::ListExpr(); result->listexpr_ = (yyval.listexpr_); }
#line 1711 "Parser.C"
    break;

  case 29: /* ListExpr: Expr  */
#line 273 "Stella.y"
         { (yyval.listexpr_) = new Stella::ListExpr(); (yyval.listexpr_)->push_back((yyvsp[0].expr_)); result->listexpr_ = (yyval.listexpr_); }
#line 1717 "Parser.C"
    break;

  case 30: /* ListExpr: Expr _COMMA ListExpr  */
#line 274 "Stella.y"
                         { (yyvsp[0].listexpr_)->push_back((yyvsp[-2].expr_)); (yyval.listexpr_) = (yyvsp[0].listexpr_); result->listexpr_ = (yyval.listexpr_); }
#line 1723 "Parser.C"
    break;

  case 31: /* MatchCase: Pattern _RDARROW Expr  */
#line 276 "Stella.y"
                                  { (yyval.matchcase_) = new Stella::AMatchCase((yyvsp[-2].pattern_), (yyvsp[0].expr_)); (yyval.matchcase_)->line_number = (yyloc).first_line; (yyval.matchcase_)->char_number = (yyloc).first_column; result->matchcase_ = (yyval.matchcase_); }
#line 1729 "Parser.C"
    break;

  case 32: /* ListMatchCase: %empty  */
#line 278 "Stella.y"
                            { (yyval.listmatchcase_) = new Stella::ListMatchCase(); result->listmatchcase_ = (yyval.listmatchcase_); }
#line 1735 "Parser.C"
    break;

  case 33: /* ListMatchCase: MatchCase  */
#line 279 "Stella.y"
              { (yyval.listmatchcase_) = new Stella::ListMatchCase(); (yyval.listmatchcase_)->push_back((yyvsp[0].matchcase_)); result->listmatchcase_ = (yyval.listmatchcase_); }
#line 1741 "Parser.C"
    break;

  case 34: /* ListMatchCase: MatchCase _SEMI ListMatchCase  */
#line 280 "Stella.y"
                                  { (yyvsp[0].listmatchcase_)->push_back((yyvsp[-2].matchcase_)); (yyval.listmatchcase_) = (yyvsp[0].listmatchcase_); result->listmatchcase_ = (yyval.listmatchcase_); }
#line 1747 "Parser.C"
    break;

  case 35: /* OptionalTyping: %empty  */
#line 282 "Stella.y"
                             { (yyval.optionaltyping_) = new Stella::NoTyping(); (yyval.optionaltyping_)->line_number = (yyloc).first_line; (yyval.optionaltyping_)->char_number = (yyloc).first_column; result->optionaltyping_ = (yyval.optionaltyping_); }
#line 1753 "Parser.C"
    break;

  case 36: /* OptionalTyping: _COLON Type  */
#line 283 "Stella.y"
                { (yyval.optionaltyping_) = new Stella::SomeTyping((yyvsp[0].type_)); (yyval.optionaltyping_)->line_number = (yyloc).first_line; (yyval.optionaltyping_)->char_number = (yyloc).first_column; result->optionaltyping_ = (yyval.optionaltyping_); }
#line 1759 "Parser.C"
    break;

  case 37: /* PatternData: %empty  */
#line 285 "Stella.y"
                          { (yyval.patterndata_) = new Stella::NoPatternData(); (yyval.patterndata_)->line_number = (yyloc).first_line; (yyval.patterndata_)->char_number = (yyloc).first_column; result->patterndata_ = (yyval.patterndata_); }
#line 1765 "Parser.C"
    break;

  case 38: /* PatternData: _EQ Pattern  */
#line 286 "Stella.y"
                { (yyval.patterndata_) = new Stella::SomePatternData((yyvsp[0].pattern_)); (yyval.patterndata_)->line_number = (yyloc).first_line; (yyval.patterndata_)->char_number = (yyloc).first_column; result->patterndata_ = (yyval.patterndata_); }
#line 1771 "Parser.C"
    break;

  case 39: /* ExprData: %empty  */
#line 288 "Stella.y"
                       { (yyval.exprdata_) = new Stella::NoExprData(); (yyval.exprdata_)->line_number = (yyloc).first_line; (yyval.exprdata_)->char_number = (yyloc).first_column; result->exprdata_ = (yyval.exprdata_); }
#line 1777 "Parser.C"
    break;

  case 40: /* ExprData: _EQ Expr  */
#line 289 "Stella.y"
             { (yyval.exprdata_) = new Stella::SomeExprData((yyvsp[0].expr_)); (yyval.exprdata_)->line_number = (yyloc).first_line; (yyval.exprdata_)->char_number = (yyloc).first_column; result->exprdata_ = (yyval.exprdata_); }
#line 1783 "Parser.C"
    break;

  case 41: /* Pattern: _SYMB_10 T_StellaIdent PatternData _SYMB_11  */
#line 291 "Stella.y"
                                                      { (yyval.pattern_) = new Stella::PatternVariant((yyvsp[-2]._string), (yyvsp[-1].patterndata_)); (yyval.pattern_)->line_number = (yyloc).first_line; (yyval.pattern_)->char_number = (yyloc).first_column; result->pattern_ = (yyval.pattern_); }
#line 1789 "Parser.C"
    break;

  case 42: /* Pattern: _LBRACE ListPattern _RBRACE  */
#line 292 "Stella.y"
                                { std::reverse((yyvsp[-1].listpattern_)->begin(),(yyvsp[-1].listpattern_)->end()) ;(yyval.pattern_) = new Stella::PatternTuple((yyvsp[-1].listpattern_)); (yyval.pattern_)->line_number = (yyloc).first_line; (yyval.pattern_)->char_number = (yyloc).first_column; result->pattern_ = (yyval.pattern_); }
#line 1795 "Parser.C"
    break;

  case 43: /* Pattern: _KW_record _LBRACE ListLabelledPattern _RBRACE  */
#line 293 "Stella.y"
                                                   { std::reverse((yyvsp[-1].listlabelledpattern_)->begin(),(yyvsp[-1].listlabelledpattern_)->end()) ;(yyval.pattern_) = new Stella::PatternRecord((yyvsp[-1].listlabelledpattern_)); (yyval.pattern_)->line_number = (yyloc).first_line; (yyval.pattern_)->char_number = (yyloc).first_column; result->pattern_ = (yyval.pattern_); }
#line 1801 "Parser.C"
    break;

  case 44: /* Pattern: _LBRACK ListPattern _RBRACK  */
#line 294 "Stella.y"
                                { std::reverse((yyvsp[-1].listpattern_)->begin(),(yyvsp[-1].listpattern_)->end()) ;(yyval.pattern_) = new Stella::PatternList((yyvsp[-1].listpattern_)); (yyval.pattern_)->line_number = (yyloc).first_line; (yyval.pattern_)->char_number = (yyloc).first_column; result->pattern_ = (yyval.pattern_); }
#line 1807 "Parser.C"
    break;

  case 45: /* Pattern: _KW_cons _LPAREN Pattern _COMMA Pattern _RPAREN  */
#line 295 "Stella.y"
                                                    { (yyval.pattern_) = new Stella::PatternCons((yyvsp[-3].pattern_), (yyvsp[-1].pattern_)); (yyval.pattern_)->line_number = (yyloc).first_line; (yyval.pattern_)->char_number = (yyloc).first_column; result->pattern_ = (yyval.pattern_); }
#line 1813 "Parser.C"
    break;

  case 46: /* Pattern: _KW_false  */
#line 296 "Stella.y"
              { (yyval.pattern_) = new Stella::PatternFalse(); (yyval.pattern_)->line_number = (yyloc).first_line; (yyval.pattern_)->char_number = (yyloc).first_column; result->pattern_ = (yyval.pattern_); }
#line 1819 "Parser.C"
    break;

  case 47: /* Pattern: _KW_true  */
#line 297 "Stella.y"
             { (yyval.pattern_) = new Stella::PatternTrue(); (yyval.pattern_)->line_number = (yyloc).first_line; (yyval.pattern_)->char_number = (yyloc).first_column; result->pattern_ = (yyval.pattern_); }
#line 1825 "Parser.C"
    break;

  case 48: /* Pattern: _INTEGER_  */
#line 298 "Stella.y"
              { (yyval.pattern_) = new Stella::PatternInt((yyvsp[0]._int)); (yyval.pattern_)->line_number = (yyloc).first_line; (yyval.pattern_)->char_number = (yyloc).first_column; result->pattern_ = (yyval.pattern_); }
#line 1831 "Parser.C"
    break;

  case 49: /* Pattern: _KW_succ _LPAREN Pattern _RPAREN  */
#line 299 "Stella.y"
                                     { (yyval.pattern_) = new Stella::PatternSucc((yyvsp[-1].pattern_)); (yyval.pattern_)->line_number = (yyloc).first_line; (yyval.pattern_)->char_number = (yyloc).first_column; result->pattern_ = (yyval.pattern_); }
#line 1837 "Parser.C"
    break;

  case 50: /* Pattern: T_StellaIdent  */
#line 300 "Stella.y"
                  { (yyval.pattern_) = new Stella::PatternVar((yyvsp[0]._string)); (yyval.pattern_)->line_number = (yyloc).first_line; (yyval.pattern_)->char_number = (yyloc).first_column; result->pattern_ = (yyval.pattern_); }
#line 1843 "Parser.C"
    break;

  case 51: /* Pattern: _LPAREN Pattern _RPAREN  */
#line 301 "Stella.y"
                            { (yyval.pattern_) = (yyvsp[-1].pattern_); (yyval.pattern_)->line_number = (yyloc).first_line; (yyval.pattern_)->char_number = (yyloc).first_column; result->pattern_ = (yyval.pattern_); }
#line 1849 "Parser.C"
    break;

  case 52: /* ListPattern: %empty  */
#line 303 "Stella.y"
                          { (yyval.listpattern_) = new Stella::ListPattern(); result->listpattern_ = (yyval.listpattern_); }
#line 1855 "Parser.C"
    break;

  case 53: /* ListPattern: Pattern  */
#line 304 "Stella.y"
            { (yyval.listpattern_) = new Stella::ListPattern(); (yyval.listpattern_)->push_back((yyvsp[0].pattern_)); result->listpattern_ = (yyval.listpattern_); }
#line 1861 "Parser.C"
    break;

  case 54: /* ListPattern: Pattern _COMMA ListPattern  */
#line 305 "Stella.y"
                               { (yyvsp[0].listpattern_)->push_back((yyvsp[-2].pattern_)); (yyval.listpattern_) = (yyvsp[0].listpattern_); result->listpattern_ = (yyval.listpattern_); }
#line 1867 "Parser.C"
    break;

  case 55: /* LabelledPattern: T_StellaIdent _EQ Pattern  */
#line 307 "Stella.y"
                                            { (yyval.labelledpattern_) = new Stella::ALabelledPattern((yyvsp[-2]._string), (yyvsp[0].pattern_)); (yyval.labelledpattern_)->line_number = (yyloc).first_line; (yyval.labelledpattern_)->char_number = (yyloc).first_column; result->labelledpattern_ = (yyval.labelledpattern_); }
#line 1873 "Parser.C"
    break;

  case 56: /* ListLabelledPattern: %empty  */
#line 309 "Stella.y"
                                  { (yyval.listlabelledpattern_) = new Stella::ListLabelledPattern(); result->listlabelledpattern_ = (yyval.listlabelledpattern_); }
#line 1879 "Parser.C"
    break;

  case 57: /* ListLabelledPattern: LabelledPattern  */
#line 310 "Stella.y"
                    { (yyval.listlabelledpattern_) = new Stella::ListLabelledPattern(); (yyval.listlabelledpattern_)->push_back((yyvsp[0].labelledpattern_)); result->listlabelledpattern_ = (yyval.listlabelledpattern_); }
#line 1885 "Parser.C"
    break;

  case 58: /* ListLabelledPattern: LabelledPattern _COMMA ListLabelledPattern  */
#line 311 "Stella.y"
                                               { (yyvsp[0].listlabelledpattern_)->push_back((yyvsp[-2].labelledpattern_)); (yyval.listlabelledpattern_) = (yyvsp[0].listlabelledpattern_); result->listlabelledpattern_ = (yyval.listlabelledpattern_); }
#line 1891 "Parser.C"
    break;

  case 59: /* Binding: T_StellaIdent _EQ Expr  */
#line 313 "Stella.y"
                                 { (yyval.binding_) = new Stella::ABinding((yyvsp[-2]._string), (yyvsp[0].expr_)); (yyval.binding_)->line_number = (yyloc).first_line; (yyval.binding_)->char_number = (yyloc).first_column; result->binding_ = (yyval.binding_); }
#line 1897 "Parser.C"
    break;

  case 60: /* ListBinding: %empty  */
#line 315 "Stella.y"
                          { (yyval.listbinding_) = new Stella::ListBinding(); result->listbinding_ = (yyval.listbinding_); }
#line 1903 "Parser.C"
    break;

  case 61: /* ListBinding: Binding  */
#line 316 "Stella.y"
            { (yyval.listbinding_) = new Stella::ListBinding(); (yyval.listbinding_)->push_back((yyvsp[0].binding_)); result->listbinding_ = (yyval.listbinding_); }
#line 1909 "Parser.C"
    break;

  case 62: /* ListBinding: Binding _COMMA ListBinding  */
#line 317 "Stella.y"
                               { (yyvsp[0].listbinding_)->push_back((yyvsp[-2].binding_)); (yyval.listbinding_) = (yyvsp[0].listbinding_); result->listbinding_ = (yyval.listbinding_); }
#line 1915 "Parser.C"
    break;

  case 63: /* Expr1: Expr2 _LT Expr2  */
#line 319 "Stella.y"
                        { (yyval.expr_) = new Stella::LessThan((yyvsp[-2].expr_), (yyvsp[0].expr_)); (yyval.expr_)->line_number = (yyloc).first_line; (yyval.expr_)->char_number = (yyloc).first_column; result->expr_ = (yyval.expr_); }
#line 1921 "Parser.C"
    break;

  case 64: /* Expr1: Expr2 _LDARROW Expr2  */
#line 320 "Stella.y"
                         { (yyval.expr_) = new Stella::LessThanOrEqual((yyvsp[-2].expr_), (yyvsp[0].expr_)); (yyval.expr_)->line_number = (yyloc).first_line; (yyval.expr_)->char_number = (yyloc).first_column; result->expr_ = (yyval.expr_); }
#line 1927 "Parser.C"
    break;

  case 65: /* Expr1: Expr2 _GT Expr2  */
#line 321 "Stella.y"
                    { (yyval.expr_) = new Stella::GreaterThan((yyvsp[-2].expr_), (yyvsp[0].expr_)); (yyval.expr_)->line_number = (yyloc).first_line; (yyval.expr_)->char_number = (yyloc).first_column; result->expr_ = (yyval.expr_); }
#line 1933 "Parser.C"
    break;

  case 66: /* Expr1: Expr2 _GTEQ Expr2  */
#line 322 "Stella.y"
                      { (yyval.expr_) = new Stella::GreaterThanOrEqual((yyvsp[-2].expr_), (yyvsp[0].expr_)); (yyval.expr_)->line_number = (yyloc).first_line; (yyval.expr_)->char_number = (yyloc).first_column; result->expr_ = (yyval.expr_); }
#line 1939 "Parser.C"
    break;

  case 67: /* Expr1: Expr2 _DEQ Expr2  */
#line 323 "Stella.y"
                     { (yyval.expr_) = new Stella::Equal((yyvsp[-2].expr_), (yyvsp[0].expr_)); (yyval.expr_)->line_number = (yyloc).first_line; (yyval.expr_)->char_number = (yyloc).first_column; result->expr_ = (yyval.expr_); }
#line 1945 "Parser.C"
    break;

  case 68: /* Expr1: Expr2 _BANGEQ Expr2  */
#line 324 "Stella.y"
                        { (yyval.expr_) = new Stella::NotEqual((yyvsp[-2].expr_), (yyvsp[0].expr_)); (yyval.expr_)->line_number = (yyloc).first_line; (yyval.expr_)->char_number = (yyloc).first_column; result->expr_ = (yyval.expr_); }
#line 1951 "Parser.C"
    break;

  case 69: /* Expr1: Expr2  */
#line 325 "Stella.y"
          { (yyval.expr_) = (yyvsp[0].expr_); (yyval.expr_)->line_number = (yyloc).first_line; (yyval.expr_)->char_number = (yyloc).first_column; result->expr_ = (yyval.expr_); }
#line 1957 "Parser.C"
    break;

  case 70: /* Expr2: Expr2 _KW_as Type  */
#line 327 "Stella.y"
                          { (yyval.expr_) = new Stella::TypeAsc((yyvsp[-2].expr_), (yyvsp[0].type_)); (yyval.expr_)->line_number = (yyloc).first_line; (yyval.expr_)->char_number = (yyloc).first_column; result->expr_ = (yyval.expr_); }
#line 1963 "Parser.C"
    break;

  case 71: /* Expr2: _KW_fn _LPAREN ListParamDecl _RPAREN _LBRACE _KW_return Expr _SEMI _RBRACE  */
#line 328 "Stella.y"
                                                                               { std::reverse((yyvsp[-6].listparamdecl_)->begin(),(yyvsp[-6].listparamdecl_)->end()) ;(yyval.expr_) = new Stella::Abstraction((yyvsp[-6].listparamdecl_), (yyvsp[-2].expr_)); (yyval.expr_)->line_number = (yyloc).first_line; (yyval.expr_)->char_number = (yyloc).first_column; result->expr_ = (yyval.expr_); }
#line 1969 "Parser.C"
    break;

  case 72: /* Expr2: _LBRACE ListExpr _RBRACE  */
#line 329 "Stella.y"
                             { std::reverse((yyvsp[-1].listexpr_)->begin(),(yyvsp[-1].listexpr_)->end()) ;(yyval.expr_) = new Stella::Tuple((yyvsp[-1].listexpr_)); (yyval.expr_)->line_number = (yyloc).first_line; (yyval.expr_)->char_number = (yyloc).first_column; result->expr_ = (yyval.expr_); }
#line 1975 "Parser.C"
    break;

  case 73: /* Expr2: _KW_record _LBRACE ListBinding _RBRACE  */
#line 330 "Stella.y"
                                           { std::reverse((yyvsp[-1].listbinding_)->begin(),(yyvsp[-1].listbinding_)->end()) ;(yyval.expr_) = new Stella::Record((yyvsp[-1].listbinding_)); (yyval.expr_)->line_number = (yyloc).first_line; (yyval.expr_)->char_number = (yyloc).first_column; result->expr_ = (yyval.expr_); }
#line 1981 "Parser.C"
    break;

  case 74: /* Expr2: _SYMB_10 T_StellaIdent ExprData _SYMB_11  */
#line 331 "Stella.y"
                                             { (yyval.expr_) = new Stella::Variant((yyvsp[-2]._string), (yyvsp[-1].exprdata_)); (yyval.expr_)->line_number = (yyloc).first_line; (yyval.expr_)->char_number = (yyloc).first_column; result->expr_ = (yyval.expr_); }
#line 1987 "Parser.C"
    break;

  case 75: /* Expr2: _KW_match Expr1 _LBRACE ListMatchCase _RBRACE  */
#line 332 "Stella.y"
                                                  { std::reverse((yyvsp[-1].listmatchcase_)->begin(),(yyvsp[-1].listmatchcase_)->end()) ;(yyval.expr_) = new Stella::Match((yyvsp[-3].expr_), (yyvsp[-1].listmatchcase_)); (yyval.expr_)->line_number = (yyloc).first_line; (yyval.expr_)->char_number = (yyloc).first_column; result->expr_ = (yyval.expr_); }
#line 1993 "Parser.C"
    break;

  case 76: /* Expr2: _LBRACK ListExpr _RBRACK  */
#line 333 "Stella.y"
                             { std::reverse((yyvsp[-1].listexpr_)->begin(),(yyvsp[-1].listexpr_)->end()) ;(yyval.expr_) = new Stella::List((yyvsp[-1].listexpr_)); (yyval.expr_)->line_number = (yyloc).first_line; (yyval.expr_)->char_number = (yyloc).first_column; result->expr_ = (yyval.expr_); }
#line 1999 "Parser.C"
    break;

  case 77: /* Expr2: Expr2 _PLUS Expr3  */
#line 334 "Stella.y"
                      { (yyval.expr_) = new Stella::Add((yyvsp[-2].expr_), (yyvsp[0].expr_)); (yyval.expr_)->line_number = (yyloc).first_line; (yyval.expr_)->char_number = (yyloc).first_column; result->expr_ = (yyval.expr_); }
#line 2005 "Parser.C"
    break;

  case 78: /* Expr2: Expr2 _KW_or Expr3  */
#line 335 "Stella.y"
                       { (yyval.expr_) = new Stella::LogicOr((yyvsp[-2].expr_), (yyvsp[0].expr_)); (yyval.expr_)->line_number = (yyloc).first_line; (yyval.expr_)->char_number = (yyloc).first_column; result->expr_ = (yyval.expr_); }
#line 2011 "Parser.C"
    break;

  case 79: /* Expr2: Expr3  */
#line 336 "Stella.y"
          { (yyval.expr_) = (yyvsp[0].expr_); (yyval.expr_)->line_number = (yyloc).first_line; (yyval.expr_)->char_number = (yyloc).first_column; result->expr_ = (yyval.expr_); }
#line 2017 "Parser.C"
    break;

  case 80: /* Expr3: Expr3 _STAR Expr4  */
#line 338 "Stella.y"
                          { (yyval.expr_) = new Stella::Multiply((yyvsp[-2].expr_), (yyvsp[0].expr_)); (yyval.expr_)->line_number = (yyloc).first_line; (yyval.expr_)->char_number = (yyloc).first_column; result->expr_ = (yyval.expr_); }
#line 2023 "Parser.C"
    break;

  case 81: /* Expr3: Expr3 _KW_and Expr4  */
#line 339 "Stella.y"
                        { (yyval.expr_) = new Stella::LogicAnd((yyvsp[-2].expr_), (yyvsp[0].expr_)); (yyval.expr_)->line_number = (yyloc).first_line; (yyval.expr_)->char_number = (yyloc).first_column; result->expr_ = (yyval.expr_); }
#line 2029 "Parser.C"
    break;

  case 82: /* Expr3: Expr4  */
#line 340 "Stella.y"
          { (yyval.expr_) = (yyvsp[0].expr_); (yyval.expr_)->line_number = (yyloc).first_line; (yyval.expr_)->char_number = (yyloc).first_column; result->expr_ = (yyval.expr_); }
#line 2035 "Parser.C"
    break;

  case 83: /* Expr4: Expr4 _LPAREN ListExpr _RPAREN  */
#line 342 "Stella.y"
                                       { std::reverse((yyvsp[-1].listexpr_)->begin(),(yyvsp[-1].listexpr_)->end()) ;(yyval.expr_) = new Stella::Application((yyvsp[-3].expr_), (yyvsp[-1].listexpr_)); (yyval.expr_)->line_number = (yyloc).first_line; (yyval.expr_)->char_number = (yyloc).first_column; result->expr_ = (yyval.expr_); }
#line 2041 "Parser.C"
    break;

  case 84: /* Expr4: Expr5  */
#line 343 "Stella.y"
          { (yyval.expr_) = (yyvsp[0].expr_); (yyval.expr_)->line_number = (yyloc).first_line; (yyval.expr_)->char_number = (yyloc).first_column; result->expr_ = (yyval.expr_); }
#line 2047 "Parser.C"
    break;

  case 85: /* Expr5: _KW_cons _LPAREN Expr _COMMA Expr _RPAREN  */
#line 345 "Stella.y"
                                                  { (yyval.expr_) = new Stella::ConsList((yyvsp[-3].expr_), (yyvsp[-1].expr_)); (yyval.expr_)->line_number = (yyloc).first_line; (yyval.expr_)->char_number = (yyloc).first_column; result->expr_ = (yyval.expr_); }
#line 2053 "Parser.C"
    break;

  case 86: /* Expr5: _SYMB_22 _LPAREN Expr _RPAREN  */
#line 346 "Stella.y"
                                  { (yyval.expr_) = new Stella::Head((yyvsp[-1].expr_)); (yyval.expr_)->line_number = (yyloc).first_line; (yyval.expr_)->char_number = (yyloc).first_column; result->expr_ = (yyval.expr_); }
#line 2059 "Parser.C"
    break;

  case 87: /* Expr5: _SYMB_23 _LPAREN Expr _RPAREN  */
#line 347 "Stella.y"
                                  { (yyval.expr_) = new Stella::IsEmpty((yyvsp[-1].expr_)); (yyval.expr_)->line_number = (yyloc).first_line; (yyval.expr_)->char_number = (yyloc).first_column; result->expr_ = (yyval.expr_); }
#line 2065 "Parser.C"
    break;

  case 88: /* Expr5: _SYMB_24 _LPAREN Expr _RPAREN  */
#line 348 "Stella.y"
                                  { (yyval.expr_) = new Stella::Tail((yyvsp[-1].expr_)); (yyval.expr_)->line_number = (yyloc).first_line; (yyval.expr_)->char_number = (yyloc).first_column; result->expr_ = (yyval.expr_); }
#line 2071 "Parser.C"
    break;

  case 89: /* Expr5: _KW_succ _LPAREN Expr _RPAREN  */
#line 349 "Stella.y"
                                  { (yyval.expr_) = new Stella::Succ((yyvsp[-1].expr_)); (yyval.expr_)->line_number = (yyloc).first_line; (yyval.expr_)->char_number = (yyloc).first_column; result->expr_ = (yyval.expr_); }
#line 2077 "Parser.C"
    break;

  case 90: /* Expr5: _KW_not _LPAREN Expr _RPAREN  */
#line 350 "Stella.y"
                                 { (yyval.expr_) = new Stella::LogicNot((yyvsp[-1].expr_)); (yyval.expr_)->line_number = (yyloc).first_line; (yyval.expr_)->char_number = (yyloc).first_column; result->expr_ = (yyval.expr_); }
#line 2083 "Parser.C"
    break;

  case 91: /* Expr5: _SYMB_25 _LPAREN Expr _RPAREN  */
#line 351 "Stella.y"
                                  { (yyval.expr_) = new Stella::Pred((yyvsp[-1].expr_)); (yyval.expr_)->line_number = (yyloc).first_line; (yyval.expr_)->char_number = (yyloc).first_column; result->expr_ = (yyval.expr_); }
#line 2089 "Parser.C"
    break;

  case 92: /* Expr5: _SYMB_26 _LPAREN Expr _RPAREN  */
#line 352 "Stella.y"
                                  { (yyval.expr_) = new Stella::IsZero((yyvsp[-1].expr_)); (yyval.expr_)->line_number = (yyloc).first_line; (yyval.expr_)->char_number = (yyloc).first_column; result->expr_ = (yyval.expr_); }
#line 2095 "Parser.C"
    break;

  case 93: /* Expr5: _KW_fix _LPAREN Expr _RPAREN  */
#line 353 "Stella.y"
                                 { (yyval.expr_) = new Stella::Fix((yyvsp[-1].expr_)); (yyval.expr_)->line_number = (yyloc).first_line; (yyval.expr_)->char_number = (yyloc).first_column; result->expr_ = (yyval.expr_); }
#line 2101 "Parser.C"
    break;

  case 94: /* Expr5: _SYMB_27 _LPAREN Expr _COMMA Expr _COMMA Expr _RPAREN  */
#line 354 "Stella.y"
                                                          { (yyval.expr_) = new Stella::NatRec((yyvsp[-5].expr_), (yyvsp[-3].expr_), (yyvsp[-1].expr_)); (yyval.expr_)->line_number = (yyloc).first_line; (yyval.expr_)->char_number = (yyloc).first_column; result->expr_ = (yyval.expr_); }
#line 2107 "Parser.C"
    break;

  case 95: /* Expr5: _KW_fold _LBRACK Type _RBRACK Expr6  */
#line 355 "Stella.y"
                                        { (yyval.expr_) = new Stella::Fold((yyvsp[-2].type_), (yyvsp[0].expr_)); (yyval.expr_)->line_number = (yyloc).first_line; (yyval.expr_)->char_number = (yyloc).first_column; result->expr_ = (yyval.expr_); }
#line 2113 "Parser.C"
    break;

  case 96: /* Expr5: _KW_unfold _LBRACK Type _RBRACK Expr6  */
#line 356 "Stella.y"
                                          { (yyval.expr_) = new Stella::Unfold((yyvsp[-2].type_), (yyvsp[0].expr_)); (yyval.expr_)->line_number = (yyloc).first_line; (yyval.expr_)->char_number = (yyloc).first_column; result->expr_ = (yyval.expr_); }
#line 2119 "Parser.C"
    break;

  case 97: /* Expr5: Expr6  */
#line 357 "Stella.y"
          { (yyval.expr_) = (yyvsp[0].expr_); (yyval.expr_)->line_number = (yyloc).first_line; (yyval.expr_)->char_number = (yyloc).first_column; result->expr_ = (yyval.expr_); }
#line 2125 "Parser.C"
    break;

  case 98: /* Expr6: Expr6 _DOT T_StellaIdent  */
#line 359 "Stella.y"
                                 { (yyval.expr_) = new Stella::DotRecord((yyvsp[-2].expr_), (yyvsp[0]._string)); (yyval.expr_)->line_number = (yyloc).first_line; (yyval.expr_)->char_number = (yyloc).first_column; result->expr_ = (yyval.expr_); }
#line 2131 "Parser.C"
    break;

  case 99: /* Expr6: Expr6 _DOT _INTEGER_  */
#line 360 "Stella.y"
                         { (yyval.expr_) = new Stella::DotTuple((yyvsp[-2].expr_), (yyvsp[0]._int)); (yyval.expr_)->line_number = (yyloc).first_line; (yyval.expr_)->char_number = (yyloc).first_column; result->expr_ = (yyval.expr_); }
#line 2137 "Parser.C"
    break;

  case 100: /* Expr6: _KW_true  */
#line 361 "Stella.y"
             { (yyval.expr_) = new Stella::ConstTrue(); (yyval.expr_)->line_number = (yyloc).first_line; (yyval.expr_)->char_number = (yyloc).first_column; result->expr_ = (yyval.expr_); }
#line 2143 "Parser.C"
    break;

  case 101: /* Expr6: _KW_false  */
#line 362 "Stella.y"
              { (yyval.expr_) = new Stella::ConstFalse(); (yyval.expr_)->line_number = (yyloc).first_line; (yyval.expr_)->char_number = (yyloc).first_column; result->expr_ = (yyval.expr_); }
#line 2149 "Parser.C"
    break;

  case 102: /* Expr6: _INTEGER_  */
#line 363 "Stella.y"
              { (yyval.expr_) = new Stella::ConstInt((yyvsp[0]._int)); (yyval.expr_)->line_number = (yyloc).first_line; (yyval.expr_)->char_number = (yyloc).first_column; result->expr_ = (yyval.expr_); }
#line 2155 "Parser.C"
    break;

  case 103: /* Expr6: T_StellaIdent  */
#line 364 "Stella.y"
                  { (yyval.expr_) = new Stella::Var((yyvsp[0]._string)); (yyval.expr_)->line_number = (yyloc).first_line; (yyval.expr_)->char_number = (yyloc).first_column; result->expr_ = (yyval.expr_); }
#line 2161 "Parser.C"
    break;

  case 104: /* Expr6: _LPAREN Expr _RPAREN  */
#line 365 "Stella.y"
                         { (yyval.expr_) = (yyvsp[-1].expr_); (yyval.expr_)->line_number = (yyloc).first_line; (yyval.expr_)->char_number = (yyloc).first_column; result->expr_ = (yyval.expr_); }
#line 2167 "Parser.C"
    break;

  case 105: /* Type: _KW_fn _LPAREN ListType _RPAREN _RARROW Type  */
#line 367 "Stella.y"
                                                    { std::reverse((yyvsp[-3].listtype_)->begin(),(yyvsp[-3].listtype_)->end()) ;(yyval.type_) = new Stella::TypeFun((yyvsp[-3].listtype_), (yyvsp[0].type_)); (yyval.type_)->line_number = (yyloc).first_line; (yyval.type_)->char_number = (yyloc).first_column; result->type_ = (yyval.type_); }
#line 2173 "Parser.C"
    break;

  case 106: /* Type: _KW_60 T_StellaIdent _DOT Type  */
#line 368 "Stella.y"
                                   { (yyval.type_) = new Stella::TypeRec((yyvsp[-2]._string), (yyvsp[0].type_)); (yyval.type_)->line_number = (yyloc).first_line; (yyval.type_)->char_number = (yyloc).first_column; result->type_ = (yyval.type_); }
#line 2179 "Parser.C"
    break;

  case 107: /* Type: Type1  */
#line 369 "Stella.y"
          { (yyval.type_) = (yyvsp[0].type_); (yyval.type_)->line_number = (yyloc).first_line; (yyval.type_)->char_number = (yyloc).first_column; result->type_ = (yyval.type_); }
#line 2185 "Parser.C"
    break;

  case 108: /* Type1: Type2 _PLUS Type2  */
#line 371 "Stella.y"
                          { (yyval.type_) = new Stella::TypeSum((yyvsp[-2].type_), (yyvsp[0].type_)); (yyval.type_)->line_number = (yyloc).first_line; (yyval.type_)->char_number = (yyloc).first_column; result->type_ = (yyval.type_); }
#line 2191 "Parser.C"
    break;

  case 109: /* Type1: Type2  */
#line 372 "Stella.y"
          { (yyval.type_) = (yyvsp[0].type_); (yyval.type_)->line_number = (yyloc).first_line; (yyval.type_)->char_number = (yyloc).first_column; result->type_ = (yyval.type_); }
#line 2197 "Parser.C"
    break;

  case 110: /* Type2: _LBRACE ListType _RBRACE  */
#line 374 "Stella.y"
                                 { std::reverse((yyvsp[-1].listtype_)->begin(),(yyvsp[-1].listtype_)->end()) ;(yyval.type_) = new Stella::TypeTuple((yyvsp[-1].listtype_)); (yyval.type_)->line_number = (yyloc).first_line; (yyval.type_)->char_number = (yyloc).first_column; result->type_ = (yyval.type_); }
#line 2203 "Parser.C"
    break;

  case 111: /* Type2: _KW_record _LBRACE ListRecordFieldType _RBRACE  */
#line 375 "Stella.y"
                                                   { std::reverse((yyvsp[-1].listrecordfieldtype_)->begin(),(yyvsp[-1].listrecordfieldtype_)->end()) ;(yyval.type_) = new Stella::TypeRecord((yyvsp[-1].listrecordfieldtype_)); (yyval.type_)->line_number = (yyloc).first_line; (yyval.type_)->char_number = (yyloc).first_column; result->type_ = (yyval.type_); }
#line 2209 "Parser.C"
    break;

  case 112: /* Type2: _KW_variant _SYMB_10 ListVariantFieldType _SYMB_11  */
#line 376 "Stella.y"
                                                       { std::reverse((yyvsp[-1].listvariantfieldtype_)->begin(),(yyvsp[-1].listvariantfieldtype_)->end()) ;(yyval.type_) = new Stella::TypeVariant((yyvsp[-1].listvariantfieldtype_)); (yyval.type_)->line_number = (yyloc).first_line; (yyval.type_)->char_number = (yyloc).first_column; result->type_ = (yyval.type_); }
#line 2215 "Parser.C"
    break;

  case 113: /* Type2: _LBRACK Type _RBRACK  */
#line 377 "Stella.y"
                         { (yyval.type_) = new Stella::TypeList((yyvsp[-1].type_)); (yyval.type_)->line_number = (yyloc).first_line; (yyval.type_)->char_number = (yyloc).first_column; result->type_ = (yyval.type_); }
#line 2221 "Parser.C"
    break;

  case 114: /* Type2: Type3  */
#line 378 "Stella.y"
          { (yyval.type_) = (yyvsp[0].type_); (yyval.type_)->line_number = (yyloc).first_line; (yyval.type_)->char_number = (yyloc).first_column; result->type_ = (yyval.type_); }
#line 2227 "Parser.C"
    break;

  case 115: /* Type3: _KW_Bool  */
#line 380 "Stella.y"
                 { (yyval.type_) = new Stella::TypeBool(); (yyval.type_)->line_number = (yyloc).first_line; (yyval.type_)->char_number = (yyloc).first_column; result->type_ = (yyval.type_); }
#line 2233 "Parser.C"
    break;

  case 116: /* Type3: _KW_Nat  */
#line 381 "Stella.y"
            { (yyval.type_) = new Stella::TypeNat(); (yyval.type_)->line_number = (yyloc).first_line; (yyval.type_)->char_number = (yyloc).first_column; result->type_ = (yyval.type_); }
#line 2239 "Parser.C"
    break;

  case 117: /* Type3: _KW_Unit  */
#line 382 "Stella.y"
             { (yyval.type_) = new Stella::TypeUnit(); (yyval.type_)->line_number = (yyloc).first_line; (yyval.type_)->char_number = (yyloc).first_column; result->type_ = (yyval.type_); }
#line 2245 "Parser.C"
    break;

  case 118: /* Type3: T_StellaIdent  */
#line 383 "Stella.y"
                  { (yyval.type_) = new Stella::TypeVar((yyvsp[0]._string)); (yyval.type_)->line_number = (yyloc).first_line; (yyval.type_)->char_number = (yyloc).first_column; result->type_ = (yyval.type_); }
#line 2251 "Parser.C"
    break;

  case 119: /* Type3: _LPAREN Type _RPAREN  */
#line 384 "Stella.y"
                         { (yyval.type_) = (yyvsp[-1].type_); (yyval.type_)->line_number = (yyloc).first_line; (yyval.type_)->char_number = (yyloc).first_column; result->type_ = (yyval.type_); }
#line 2257 "Parser.C"
    break;

  case 120: /* ListType: %empty  */
#line 386 "Stella.y"
                       { (yyval.listtype_) = new Stella::ListType(); result->listtype_ = (yyval.listtype_); }
#line 2263 "Parser.C"
    break;

  case 121: /* ListType: Type  */
#line 387 "Stella.y"
         { (yyval.listtype_) = new Stella::ListType(); (yyval.listtype_)->push_back((yyvsp[0].type_)); result->listtype_ = (yyval.listtype_); }
#line 2269 "Parser.C"
    break;

  case 122: /* ListType: Type _COMMA ListType  */
#line 388 "Stella.y"
                         { (yyvsp[0].listtype_)->push_back((yyvsp[-2].type_)); (yyval.listtype_) = (yyvsp[0].listtype_); result->listtype_ = (yyval.listtype_); }
#line 2275 "Parser.C"
    break;

  case 123: /* VariantFieldType: T_StellaIdent OptionalTyping  */
#line 390 "Stella.y"
                                                { (yyval.variantfieldtype_) = new Stella::AVariantFieldType((yyvsp[-1]._string), (yyvsp[0].optionaltyping_)); (yyval.variantfieldtype_)->line_number = (yyloc).first_line; (yyval.variantfieldtype_)->char_number = (yyloc).first_column; result->variantfieldtype_ = (yyval.variantfieldtype_); }
#line 2281 "Parser.C"
    break;

  case 124: /* ListVariantFieldType: %empty  */
#line 392 "Stella.y"
                                   { (yyval.listvariantfieldtype_) = new Stella::ListVariantFieldType(); result->listvariantfieldtype_ = (yyval.listvariantfieldtype_); }
#line 2287 "Parser.C"
    break;

  case 125: /* ListVariantFieldType: VariantFieldType  */
#line 393 "Stella.y"
                     { (yyval.listvariantfieldtype_) = new Stella::ListVariantFieldType(); (yyval.listvariantfieldtype_)->push_back((yyvsp[0].variantfieldtype_)); result->listvariantfieldtype_ = (yyval.listvariantfieldtype_); }
#line 2293 "Parser.C"
    break;

  case 126: /* ListVariantFieldType: VariantFieldType _COMMA ListVariantFieldType  */
#line 394 "Stella.y"
                                                 { (yyvsp[0].listvariantfieldtype_)->push_back((yyvsp[-2].variantfieldtype_)); (yyval.listvariantfieldtype_) = (yyvsp[0].listvariantfieldtype_); result->listvariantfieldtype_ = (yyval.listvariantfieldtype_); }
#line 2299 "Parser.C"
    break;

  case 127: /* RecordFieldType: T_StellaIdent _COLON Type  */
#line 396 "Stella.y"
                                            { (yyval.recordfieldtype_) = new Stella::ARecordFieldType((yyvsp[-2]._string), (yyvsp[0].type_)); (yyval.recordfieldtype_)->line_number = (yyloc).first_line; (yyval.recordfieldtype_)->char_number = (yyloc).first_column; result->recordfieldtype_ = (yyval.recordfieldtype_); }
#line 2305 "Parser.C"
    break;

  case 128: /* ListRecordFieldType: %empty  */
#line 398 "Stella.y"
                                  { (yyval.listrecordfieldtype_) = new Stella::ListRecordFieldType(); result->listrecordfieldtype_ = (yyval.listrecordfieldtype_); }
#line 2311 "Parser.C"
    break;

  case 129: /* ListRecordFieldType: RecordFieldType  */
#line 399 "Stella.y"
                    { (yyval.listrecordfieldtype_) = new Stella::ListRecordFieldType(); (yyval.listrecordfieldtype_)->push_back((yyvsp[0].recordfieldtype_)); result->listrecordfieldtype_ = (yyval.listrecordfieldtype_); }
#line 2317 "Parser.C"
    break;

  case 130: /* ListRecordFieldType: RecordFieldType _COMMA ListRecordFieldType  */
#line 400 "Stella.y"
                                               { (yyvsp[0].listrecordfieldtype_)->push_back((yyvsp[-2].recordfieldtype_)); (yyval.listrecordfieldtype_) = (yyvsp[0].listrecordfieldtype_); result->listrecordfieldtype_ = (yyval.listrecordfieldtype_); }
#line 2323 "Parser.C"
    break;


#line 2327 "Parser.C"

      default: break;
    }
  /* User semantic actions sometimes alter yychar, and that requires
     that yytoken be updated with the new translation.  We take the
     approach of translating immediately before every use of yytoken.
     One alternative is translating here after every semantic action,
     but that translation would be missed if the semantic action invokes
     YYABORT, YYACCEPT, or YYERROR immediately after altering yychar or
     if it invokes YYBACKUP.  In the case of YYABORT or YYACCEPT, an
     incorrect destructor might then be invoked immediately.  In the
     case of YYERROR or YYBACKUP, subsequent parser actions might lead
     to an incorrect destructor call or verbose syntax error message
     before the lookahead is translated.  */
  YY_SYMBOL_PRINT ("-> $$ =", YY_CAST (yysymbol_kind_t, yyr1[yyn]), &yyval, &yyloc);

  YYPOPSTACK (yylen);
  yylen = 0;

  *++yyvsp = yyval;
  *++yylsp = yyloc;

  /* Now 'shift' the result of the reduction.  Determine what state
     that goes to, based on the state we popped back to and the rule
     number reduced by.  */
  {
    const int yylhs = yyr1[yyn] - YYNTOKENS;
    const int yyi = yypgoto[yylhs] + *yyssp;
    yystate = (0 <= yyi && yyi <= YYLAST && yycheck[yyi] == *yyssp
               ? yytable[yyi]
               : yydefgoto[yylhs]);
  }

  goto yynewstate;


/*--------------------------------------.
| yyerrlab -- here on detecting error.  |
`--------------------------------------*/
yyerrlab:
  /* Make sure we have latest lookahead translation.  See comments at
     user semantic actions for why this is necessary.  */
  yytoken = yychar == YYEMPTY ? YYSYMBOL_YYEMPTY : YYTRANSLATE (yychar);
  /* If not already recovering from an error, report this error.  */
  if (!yyerrstatus)
    {
      ++yynerrs;
      yyerror (&yylloc, scanner, result, YY_("syntax error"));
    }

  yyerror_range[1] = yylloc;
  if (yyerrstatus == 3)
    {
      /* If just tried and failed to reuse lookahead token after an
         error, discard it.  */

      if (yychar <= YYEOF)
        {
          /* Return failure if at end of input.  */
          if (yychar == YYEOF)
            YYABORT;
        }
      else
        {
          yydestruct ("Error: discarding",
                      yytoken, &yylval, &yylloc, scanner, result);
          yychar = YYEMPTY;
        }
    }

  /* Else will try to reuse lookahead token after shifting the error
     token.  */
  goto yyerrlab1;


/*---------------------------------------------------.
| yyerrorlab -- error raised explicitly by YYERROR.  |
`---------------------------------------------------*/
yyerrorlab:
  /* Pacify compilers when the user code never invokes YYERROR and the
     label yyerrorlab therefore never appears in user code.  */
  if (0)
    YYERROR;
  ++yynerrs;

  /* Do not reclaim the symbols of the rule whose action triggered
     this YYERROR.  */
  YYPOPSTACK (yylen);
  yylen = 0;
  YY_STACK_PRINT (yyss, yyssp);
  yystate = *yyssp;
  goto yyerrlab1;


/*-------------------------------------------------------------.
| yyerrlab1 -- common code for both syntax error and YYERROR.  |
`-------------------------------------------------------------*/
yyerrlab1:
  yyerrstatus = 3;      /* Each real token shifted decrements this.  */

  /* Pop stack until we find a state that shifts the error token.  */
  for (;;)
    {
      yyn = yypact[yystate];
      if (!yypact_value_is_default (yyn))
        {
          yyn += YYSYMBOL_YYerror;
          if (0 <= yyn && yyn <= YYLAST && yycheck[yyn] == YYSYMBOL_YYerror)
            {
              yyn = yytable[yyn];
              if (0 < yyn)
                break;
            }
        }

      /* Pop the current state because it cannot handle the error token.  */
      if (yyssp == yyss)
        YYABORT;

      yyerror_range[1] = *yylsp;
      yydestruct ("Error: popping",
                  YY_ACCESSING_SYMBOL (yystate), yyvsp, yylsp, scanner, result);
      YYPOPSTACK (1);
      yystate = *yyssp;
      YY_STACK_PRINT (yyss, yyssp);
    }

  YY_IGNORE_MAYBE_UNINITIALIZED_BEGIN
  *++yyvsp = yylval;
  YY_IGNORE_MAYBE_UNINITIALIZED_END

  yyerror_range[2] = yylloc;
  ++yylsp;
  YYLLOC_DEFAULT (*yylsp, yyerror_range, 2);

  /* Shift the error token.  */
  YY_SYMBOL_PRINT ("Shifting", YY_ACCESSING_SYMBOL (yyn), yyvsp, yylsp);

  yystate = yyn;
  goto yynewstate;


/*-------------------------------------.
| yyacceptlab -- YYACCEPT comes here.  |
`-------------------------------------*/
yyacceptlab:
  yyresult = 0;
  goto yyreturnlab;


/*-----------------------------------.
| yyabortlab -- YYABORT comes here.  |
`-----------------------------------*/
yyabortlab:
  yyresult = 1;
  goto yyreturnlab;


/*-----------------------------------------------------------.
| yyexhaustedlab -- YYNOMEM (memory exhaustion) comes here.  |
`-----------------------------------------------------------*/
yyexhaustedlab:
  yyerror (&yylloc, scanner, result, YY_("memory exhausted"));
  yyresult = 2;
  goto yyreturnlab;


/*----------------------------------------------------------.
| yyreturnlab -- parsing is finished, clean up and return.  |
`----------------------------------------------------------*/
yyreturnlab:
  if (yychar != YYEMPTY)
    {
      /* Make sure we have latest lookahead translation.  See comments at
         user semantic actions for why this is necessary.  */
      yytoken = YYTRANSLATE (yychar);
      yydestruct ("Cleanup: discarding lookahead",
                  yytoken, &yylval, &yylloc, scanner, result);
    }
  /* Do not reclaim the symbols of the rule whose action triggered
     this YYABORT or YYACCEPT.  */
  YYPOPSTACK (yylen);
  YY_STACK_PRINT (yyss, yyssp);
  while (yyssp != yyss)
    {
      yydestruct ("Cleanup: popping",
                  YY_ACCESSING_SYMBOL (+*yyssp), yyvsp, yylsp, scanner, result);
      YYPOPSTACK (1);
    }
#ifndef yyoverflow
  if (yyss != yyssa)
    YYSTACK_FREE (yyss);
#endif

  return yyresult;
}

#line 405 "Stella.y"


namespace Stella
{
/* Entrypoint: parse Program* from file. */
Program* pProgram(FILE *inp)
{
  YYSTYPE result;
  yyscan_t scanner = Stella_initialize_lexer(inp);
  if (!scanner) {
    fprintf(stderr, "Failed to initialize lexer.\n");
    return 0;
  }
  int error = yyparse(scanner, &result);
  Stellalex_destroy(scanner);
  if (error)
  { /* Failure */
    return 0;
  }
  else
  { /* Success */
    return result.program_;
  }
}

/* Entrypoint: parse Program* from string. */
Program* psProgram(const char *str)
{
  YYSTYPE result;
  yyscan_t scanner = Stella_initialize_lexer(0);
  if (!scanner) {
    fprintf(stderr, "Failed to initialize lexer.\n");
    return 0;
  }
  YY_BUFFER_STATE buf = Stella_scan_string(str, scanner);
  int error = yyparse(scanner, &result);
  Stella_delete_buffer(buf, scanner);
  Stellalex_destroy(scanner);
  if (error)
  { /* Failure */
    return 0;
  }
  else
  { /* Success */
    return result.program_;
  }
}

/* Entrypoint: parse ListStellaIdent* from file. */
ListStellaIdent* pListStellaIdent(FILE *inp)
{
  YYSTYPE result;
  yyscan_t scanner = Stella_initialize_lexer(inp);
  if (!scanner) {
    fprintf(stderr, "Failed to initialize lexer.\n");
    return 0;
  }
  int error = yyparse(scanner, &result);
  Stellalex_destroy(scanner);
  if (error)
  { /* Failure */
    return 0;
  }
  else
  { /* Success */
std::reverse(result.liststellaident_->begin(), result.liststellaident_->end());
    return result.liststellaident_;
  }
}

/* Entrypoint: parse ListStellaIdent* from string. */
ListStellaIdent* psListStellaIdent(const char *str)
{
  YYSTYPE result;
  yyscan_t scanner = Stella_initialize_lexer(0);
  if (!scanner) {
    fprintf(stderr, "Failed to initialize lexer.\n");
    return 0;
  }
  YY_BUFFER_STATE buf = Stella_scan_string(str, scanner);
  int error = yyparse(scanner, &result);
  Stella_delete_buffer(buf, scanner);
  Stellalex_destroy(scanner);
  if (error)
  { /* Failure */
    return 0;
  }
  else
  { /* Success */
std::reverse(result.liststellaident_->begin(), result.liststellaident_->end());
    return result.liststellaident_;
  }
}

/* Entrypoint: parse LanguageDecl* from file. */
LanguageDecl* pLanguageDecl(FILE *inp)
{
  YYSTYPE result;
  yyscan_t scanner = Stella_initialize_lexer(inp);
  if (!scanner) {
    fprintf(stderr, "Failed to initialize lexer.\n");
    return 0;
  }
  int error = yyparse(scanner, &result);
  Stellalex_destroy(scanner);
  if (error)
  { /* Failure */
    return 0;
  }
  else
  { /* Success */
    return result.languagedecl_;
  }
}

/* Entrypoint: parse LanguageDecl* from string. */
LanguageDecl* psLanguageDecl(const char *str)
{
  YYSTYPE result;
  yyscan_t scanner = Stella_initialize_lexer(0);
  if (!scanner) {
    fprintf(stderr, "Failed to initialize lexer.\n");
    return 0;
  }
  YY_BUFFER_STATE buf = Stella_scan_string(str, scanner);
  int error = yyparse(scanner, &result);
  Stella_delete_buffer(buf, scanner);
  Stellalex_destroy(scanner);
  if (error)
  { /* Failure */
    return 0;
  }
  else
  { /* Success */
    return result.languagedecl_;
  }
}

/* Entrypoint: parse Extension* from file. */
Extension* pExtension(FILE *inp)
{
  YYSTYPE result;
  yyscan_t scanner = Stella_initialize_lexer(inp);
  if (!scanner) {
    fprintf(stderr, "Failed to initialize lexer.\n");
    return 0;
  }
  int error = yyparse(scanner, &result);
  Stellalex_destroy(scanner);
  if (error)
  { /* Failure */
    return 0;
  }
  else
  { /* Success */
    return result.extension_;
  }
}

/* Entrypoint: parse Extension* from string. */
Extension* psExtension(const char *str)
{
  YYSTYPE result;
  yyscan_t scanner = Stella_initialize_lexer(0);
  if (!scanner) {
    fprintf(stderr, "Failed to initialize lexer.\n");
    return 0;
  }
  YY_BUFFER_STATE buf = Stella_scan_string(str, scanner);
  int error = yyparse(scanner, &result);
  Stella_delete_buffer(buf, scanner);
  Stellalex_destroy(scanner);
  if (error)
  { /* Failure */
    return 0;
  }
  else
  { /* Success */
    return result.extension_;
  }
}

/* Entrypoint: parse ListExtensionName* from file. */
ListExtensionName* pListExtensionName(FILE *inp)
{
  YYSTYPE result;
  yyscan_t scanner = Stella_initialize_lexer(inp);
  if (!scanner) {
    fprintf(stderr, "Failed to initialize lexer.\n");
    return 0;
  }
  int error = yyparse(scanner, &result);
  Stellalex_destroy(scanner);
  if (error)
  { /* Failure */
    return 0;
  }
  else
  { /* Success */
std::reverse(result.listextensionname_->begin(), result.listextensionname_->end());
    return result.listextensionname_;
  }
}

/* Entrypoint: parse ListExtensionName* from string. */
ListExtensionName* psListExtensionName(const char *str)
{
  YYSTYPE result;
  yyscan_t scanner = Stella_initialize_lexer(0);
  if (!scanner) {
    fprintf(stderr, "Failed to initialize lexer.\n");
    return 0;
  }
  YY_BUFFER_STATE buf = Stella_scan_string(str, scanner);
  int error = yyparse(scanner, &result);
  Stella_delete_buffer(buf, scanner);
  Stellalex_destroy(scanner);
  if (error)
  { /* Failure */
    return 0;
  }
  else
  { /* Success */
std::reverse(result.listextensionname_->begin(), result.listextensionname_->end());
    return result.listextensionname_;
  }
}

/* Entrypoint: parse ListExtension* from file. */
ListExtension* pListExtension(FILE *inp)
{
  YYSTYPE result;
  yyscan_t scanner = Stella_initialize_lexer(inp);
  if (!scanner) {
    fprintf(stderr, "Failed to initialize lexer.\n");
    return 0;
  }
  int error = yyparse(scanner, &result);
  Stellalex_destroy(scanner);
  if (error)
  { /* Failure */
    return 0;
  }
  else
  { /* Success */
    return result.listextension_;
  }
}

/* Entrypoint: parse ListExtension* from string. */
ListExtension* psListExtension(const char *str)
{
  YYSTYPE result;
  yyscan_t scanner = Stella_initialize_lexer(0);
  if (!scanner) {
    fprintf(stderr, "Failed to initialize lexer.\n");
    return 0;
  }
  YY_BUFFER_STATE buf = Stella_scan_string(str, scanner);
  int error = yyparse(scanner, &result);
  Stella_delete_buffer(buf, scanner);
  Stellalex_destroy(scanner);
  if (error)
  { /* Failure */
    return 0;
  }
  else
  { /* Success */
    return result.listextension_;
  }
}

/* Entrypoint: parse Decl* from file. */
Decl* pDecl(FILE *inp)
{
  YYSTYPE result;
  yyscan_t scanner = Stella_initialize_lexer(inp);
  if (!scanner) {
    fprintf(stderr, "Failed to initialize lexer.\n");
    return 0;
  }
  int error = yyparse(scanner, &result);
  Stellalex_destroy(scanner);
  if (error)
  { /* Failure */
    return 0;
  }
  else
  { /* Success */
    return result.decl_;
  }
}

/* Entrypoint: parse Decl* from string. */
Decl* psDecl(const char *str)
{
  YYSTYPE result;
  yyscan_t scanner = Stella_initialize_lexer(0);
  if (!scanner) {
    fprintf(stderr, "Failed to initialize lexer.\n");
    return 0;
  }
  YY_BUFFER_STATE buf = Stella_scan_string(str, scanner);
  int error = yyparse(scanner, &result);
  Stella_delete_buffer(buf, scanner);
  Stellalex_destroy(scanner);
  if (error)
  { /* Failure */
    return 0;
  }
  else
  { /* Success */
    return result.decl_;
  }
}

/* Entrypoint: parse ListDecl* from file. */
ListDecl* pListDecl(FILE *inp)
{
  YYSTYPE result;
  yyscan_t scanner = Stella_initialize_lexer(inp);
  if (!scanner) {
    fprintf(stderr, "Failed to initialize lexer.\n");
    return 0;
  }
  int error = yyparse(scanner, &result);
  Stellalex_destroy(scanner);
  if (error)
  { /* Failure */
    return 0;
  }
  else
  { /* Success */
    return result.listdecl_;
  }
}

/* Entrypoint: parse ListDecl* from string. */
ListDecl* psListDecl(const char *str)
{
  YYSTYPE result;
  yyscan_t scanner = Stella_initialize_lexer(0);
  if (!scanner) {
    fprintf(stderr, "Failed to initialize lexer.\n");
    return 0;
  }
  YY_BUFFER_STATE buf = Stella_scan_string(str, scanner);
  int error = yyparse(scanner, &result);
  Stella_delete_buffer(buf, scanner);
  Stellalex_destroy(scanner);
  if (error)
  { /* Failure */
    return 0;
  }
  else
  { /* Success */
    return result.listdecl_;
  }
}

/* Entrypoint: parse LocalDecl* from file. */
LocalDecl* pLocalDecl(FILE *inp)
{
  YYSTYPE result;
  yyscan_t scanner = Stella_initialize_lexer(inp);
  if (!scanner) {
    fprintf(stderr, "Failed to initialize lexer.\n");
    return 0;
  }
  int error = yyparse(scanner, &result);
  Stellalex_destroy(scanner);
  if (error)
  { /* Failure */
    return 0;
  }
  else
  { /* Success */
    return result.localdecl_;
  }
}

/* Entrypoint: parse LocalDecl* from string. */
LocalDecl* psLocalDecl(const char *str)
{
  YYSTYPE result;
  yyscan_t scanner = Stella_initialize_lexer(0);
  if (!scanner) {
    fprintf(stderr, "Failed to initialize lexer.\n");
    return 0;
  }
  YY_BUFFER_STATE buf = Stella_scan_string(str, scanner);
  int error = yyparse(scanner, &result);
  Stella_delete_buffer(buf, scanner);
  Stellalex_destroy(scanner);
  if (error)
  { /* Failure */
    return 0;
  }
  else
  { /* Success */
    return result.localdecl_;
  }
}

/* Entrypoint: parse ListLocalDecl* from file. */
ListLocalDecl* pListLocalDecl(FILE *inp)
{
  YYSTYPE result;
  yyscan_t scanner = Stella_initialize_lexer(inp);
  if (!scanner) {
    fprintf(stderr, "Failed to initialize lexer.\n");
    return 0;
  }
  int error = yyparse(scanner, &result);
  Stellalex_destroy(scanner);
  if (error)
  { /* Failure */
    return 0;
  }
  else
  { /* Success */
    return result.listlocaldecl_;
  }
}

/* Entrypoint: parse ListLocalDecl* from string. */
ListLocalDecl* psListLocalDecl(const char *str)
{
  YYSTYPE result;
  yyscan_t scanner = Stella_initialize_lexer(0);
  if (!scanner) {
    fprintf(stderr, "Failed to initialize lexer.\n");
    return 0;
  }
  YY_BUFFER_STATE buf = Stella_scan_string(str, scanner);
  int error = yyparse(scanner, &result);
  Stella_delete_buffer(buf, scanner);
  Stellalex_destroy(scanner);
  if (error)
  { /* Failure */
    return 0;
  }
  else
  { /* Success */
    return result.listlocaldecl_;
  }
}

/* Entrypoint: parse Annotation* from file. */
Annotation* pAnnotation(FILE *inp)
{
  YYSTYPE result;
  yyscan_t scanner = Stella_initialize_lexer(inp);
  if (!scanner) {
    fprintf(stderr, "Failed to initialize lexer.\n");
    return 0;
  }
  int error = yyparse(scanner, &result);
  Stellalex_destroy(scanner);
  if (error)
  { /* Failure */
    return 0;
  }
  else
  { /* Success */
    return result.annotation_;
  }
}

/* Entrypoint: parse Annotation* from string. */
Annotation* psAnnotation(const char *str)
{
  YYSTYPE result;
  yyscan_t scanner = Stella_initialize_lexer(0);
  if (!scanner) {
    fprintf(stderr, "Failed to initialize lexer.\n");
    return 0;
  }
  YY_BUFFER_STATE buf = Stella_scan_string(str, scanner);
  int error = yyparse(scanner, &result);
  Stella_delete_buffer(buf, scanner);
  Stellalex_destroy(scanner);
  if (error)
  { /* Failure */
    return 0;
  }
  else
  { /* Success */
    return result.annotation_;
  }
}

/* Entrypoint: parse ListAnnotation* from file. */
ListAnnotation* pListAnnotation(FILE *inp)
{
  YYSTYPE result;
  yyscan_t scanner = Stella_initialize_lexer(inp);
  if (!scanner) {
    fprintf(stderr, "Failed to initialize lexer.\n");
    return 0;
  }
  int error = yyparse(scanner, &result);
  Stellalex_destroy(scanner);
  if (error)
  { /* Failure */
    return 0;
  }
  else
  { /* Success */
    return result.listannotation_;
  }
}

/* Entrypoint: parse ListAnnotation* from string. */
ListAnnotation* psListAnnotation(const char *str)
{
  YYSTYPE result;
  yyscan_t scanner = Stella_initialize_lexer(0);
  if (!scanner) {
    fprintf(stderr, "Failed to initialize lexer.\n");
    return 0;
  }
  YY_BUFFER_STATE buf = Stella_scan_string(str, scanner);
  int error = yyparse(scanner, &result);
  Stella_delete_buffer(buf, scanner);
  Stellalex_destroy(scanner);
  if (error)
  { /* Failure */
    return 0;
  }
  else
  { /* Success */
    return result.listannotation_;
  }
}

/* Entrypoint: parse ParamDecl* from file. */
ParamDecl* pParamDecl(FILE *inp)
{
  YYSTYPE result;
  yyscan_t scanner = Stella_initialize_lexer(inp);
  if (!scanner) {
    fprintf(stderr, "Failed to initialize lexer.\n");
    return 0;
  }
  int error = yyparse(scanner, &result);
  Stellalex_destroy(scanner);
  if (error)
  { /* Failure */
    return 0;
  }
  else
  { /* Success */
    return result.paramdecl_;
  }
}

/* Entrypoint: parse ParamDecl* from string. */
ParamDecl* psParamDecl(const char *str)
{
  YYSTYPE result;
  yyscan_t scanner = Stella_initialize_lexer(0);
  if (!scanner) {
    fprintf(stderr, "Failed to initialize lexer.\n");
    return 0;
  }
  YY_BUFFER_STATE buf = Stella_scan_string(str, scanner);
  int error = yyparse(scanner, &result);
  Stella_delete_buffer(buf, scanner);
  Stellalex_destroy(scanner);
  if (error)
  { /* Failure */
    return 0;
  }
  else
  { /* Success */
    return result.paramdecl_;
  }
}

/* Entrypoint: parse ListParamDecl* from file. */
ListParamDecl* pListParamDecl(FILE *inp)
{
  YYSTYPE result;
  yyscan_t scanner = Stella_initialize_lexer(inp);
  if (!scanner) {
    fprintf(stderr, "Failed to initialize lexer.\n");
    return 0;
  }
  int error = yyparse(scanner, &result);
  Stellalex_destroy(scanner);
  if (error)
  { /* Failure */
    return 0;
  }
  else
  { /* Success */
std::reverse(result.listparamdecl_->begin(), result.listparamdecl_->end());
    return result.listparamdecl_;
  }
}

/* Entrypoint: parse ListParamDecl* from string. */
ListParamDecl* psListParamDecl(const char *str)
{
  YYSTYPE result;
  yyscan_t scanner = Stella_initialize_lexer(0);
  if (!scanner) {
    fprintf(stderr, "Failed to initialize lexer.\n");
    return 0;
  }
  YY_BUFFER_STATE buf = Stella_scan_string(str, scanner);
  int error = yyparse(scanner, &result);
  Stella_delete_buffer(buf, scanner);
  Stellalex_destroy(scanner);
  if (error)
  { /* Failure */
    return 0;
  }
  else
  { /* Success */
std::reverse(result.listparamdecl_->begin(), result.listparamdecl_->end());
    return result.listparamdecl_;
  }
}

/* Entrypoint: parse ReturnType* from file. */
ReturnType* pReturnType(FILE *inp)
{
  YYSTYPE result;
  yyscan_t scanner = Stella_initialize_lexer(inp);
  if (!scanner) {
    fprintf(stderr, "Failed to initialize lexer.\n");
    return 0;
  }
  int error = yyparse(scanner, &result);
  Stellalex_destroy(scanner);
  if (error)
  { /* Failure */
    return 0;
  }
  else
  { /* Success */
    return result.returntype_;
  }
}

/* Entrypoint: parse ReturnType* from string. */
ReturnType* psReturnType(const char *str)
{
  YYSTYPE result;
  yyscan_t scanner = Stella_initialize_lexer(0);
  if (!scanner) {
    fprintf(stderr, "Failed to initialize lexer.\n");
    return 0;
  }
  YY_BUFFER_STATE buf = Stella_scan_string(str, scanner);
  int error = yyparse(scanner, &result);
  Stella_delete_buffer(buf, scanner);
  Stellalex_destroy(scanner);
  if (error)
  { /* Failure */
    return 0;
  }
  else
  { /* Success */
    return result.returntype_;
  }
}

/* Entrypoint: parse ThrowType* from file. */
ThrowType* pThrowType(FILE *inp)
{
  YYSTYPE result;
  yyscan_t scanner = Stella_initialize_lexer(inp);
  if (!scanner) {
    fprintf(stderr, "Failed to initialize lexer.\n");
    return 0;
  }
  int error = yyparse(scanner, &result);
  Stellalex_destroy(scanner);
  if (error)
  { /* Failure */
    return 0;
  }
  else
  { /* Success */
    return result.throwtype_;
  }
}

/* Entrypoint: parse ThrowType* from string. */
ThrowType* psThrowType(const char *str)
{
  YYSTYPE result;
  yyscan_t scanner = Stella_initialize_lexer(0);
  if (!scanner) {
    fprintf(stderr, "Failed to initialize lexer.\n");
    return 0;
  }
  YY_BUFFER_STATE buf = Stella_scan_string(str, scanner);
  int error = yyparse(scanner, &result);
  Stella_delete_buffer(buf, scanner);
  Stellalex_destroy(scanner);
  if (error)
  { /* Failure */
    return 0;
  }
  else
  { /* Success */
    return result.throwtype_;
  }
}

/* Entrypoint: parse Expr* from file. */
Expr* pExpr(FILE *inp)
{
  YYSTYPE result;
  yyscan_t scanner = Stella_initialize_lexer(inp);
  if (!scanner) {
    fprintf(stderr, "Failed to initialize lexer.\n");
    return 0;
  }
  int error = yyparse(scanner, &result);
  Stellalex_destroy(scanner);
  if (error)
  { /* Failure */
    return 0;
  }
  else
  { /* Success */
    return result.expr_;
  }
}

/* Entrypoint: parse Expr* from string. */
Expr* psExpr(const char *str)
{
  YYSTYPE result;
  yyscan_t scanner = Stella_initialize_lexer(0);
  if (!scanner) {
    fprintf(stderr, "Failed to initialize lexer.\n");
    return 0;
  }
  YY_BUFFER_STATE buf = Stella_scan_string(str, scanner);
  int error = yyparse(scanner, &result);
  Stella_delete_buffer(buf, scanner);
  Stellalex_destroy(scanner);
  if (error)
  { /* Failure */
    return 0;
  }
  else
  { /* Success */
    return result.expr_;
  }
}

/* Entrypoint: parse ListExpr* from file. */
ListExpr* pListExpr(FILE *inp)
{
  YYSTYPE result;
  yyscan_t scanner = Stella_initialize_lexer(inp);
  if (!scanner) {
    fprintf(stderr, "Failed to initialize lexer.\n");
    return 0;
  }
  int error = yyparse(scanner, &result);
  Stellalex_destroy(scanner);
  if (error)
  { /* Failure */
    return 0;
  }
  else
  { /* Success */
std::reverse(result.listexpr_->begin(), result.listexpr_->end());
    return result.listexpr_;
  }
}

/* Entrypoint: parse ListExpr* from string. */
ListExpr* psListExpr(const char *str)
{
  YYSTYPE result;
  yyscan_t scanner = Stella_initialize_lexer(0);
  if (!scanner) {
    fprintf(stderr, "Failed to initialize lexer.\n");
    return 0;
  }
  YY_BUFFER_STATE buf = Stella_scan_string(str, scanner);
  int error = yyparse(scanner, &result);
  Stella_delete_buffer(buf, scanner);
  Stellalex_destroy(scanner);
  if (error)
  { /* Failure */
    return 0;
  }
  else
  { /* Success */
std::reverse(result.listexpr_->begin(), result.listexpr_->end());
    return result.listexpr_;
  }
}

/* Entrypoint: parse MatchCase* from file. */
MatchCase* pMatchCase(FILE *inp)
{
  YYSTYPE result;
  yyscan_t scanner = Stella_initialize_lexer(inp);
  if (!scanner) {
    fprintf(stderr, "Failed to initialize lexer.\n");
    return 0;
  }
  int error = yyparse(scanner, &result);
  Stellalex_destroy(scanner);
  if (error)
  { /* Failure */
    return 0;
  }
  else
  { /* Success */
    return result.matchcase_;
  }
}

/* Entrypoint: parse MatchCase* from string. */
MatchCase* psMatchCase(const char *str)
{
  YYSTYPE result;
  yyscan_t scanner = Stella_initialize_lexer(0);
  if (!scanner) {
    fprintf(stderr, "Failed to initialize lexer.\n");
    return 0;
  }
  YY_BUFFER_STATE buf = Stella_scan_string(str, scanner);
  int error = yyparse(scanner, &result);
  Stella_delete_buffer(buf, scanner);
  Stellalex_destroy(scanner);
  if (error)
  { /* Failure */
    return 0;
  }
  else
  { /* Success */
    return result.matchcase_;
  }
}

/* Entrypoint: parse ListMatchCase* from file. */
ListMatchCase* pListMatchCase(FILE *inp)
{
  YYSTYPE result;
  yyscan_t scanner = Stella_initialize_lexer(inp);
  if (!scanner) {
    fprintf(stderr, "Failed to initialize lexer.\n");
    return 0;
  }
  int error = yyparse(scanner, &result);
  Stellalex_destroy(scanner);
  if (error)
  { /* Failure */
    return 0;
  }
  else
  { /* Success */
std::reverse(result.listmatchcase_->begin(), result.listmatchcase_->end());
    return result.listmatchcase_;
  }
}

/* Entrypoint: parse ListMatchCase* from string. */
ListMatchCase* psListMatchCase(const char *str)
{
  YYSTYPE result;
  yyscan_t scanner = Stella_initialize_lexer(0);
  if (!scanner) {
    fprintf(stderr, "Failed to initialize lexer.\n");
    return 0;
  }
  YY_BUFFER_STATE buf = Stella_scan_string(str, scanner);
  int error = yyparse(scanner, &result);
  Stella_delete_buffer(buf, scanner);
  Stellalex_destroy(scanner);
  if (error)
  { /* Failure */
    return 0;
  }
  else
  { /* Success */
std::reverse(result.listmatchcase_->begin(), result.listmatchcase_->end());
    return result.listmatchcase_;
  }
}

/* Entrypoint: parse OptionalTyping* from file. */
OptionalTyping* pOptionalTyping(FILE *inp)
{
  YYSTYPE result;
  yyscan_t scanner = Stella_initialize_lexer(inp);
  if (!scanner) {
    fprintf(stderr, "Failed to initialize lexer.\n");
    return 0;
  }
  int error = yyparse(scanner, &result);
  Stellalex_destroy(scanner);
  if (error)
  { /* Failure */
    return 0;
  }
  else
  { /* Success */
    return result.optionaltyping_;
  }
}

/* Entrypoint: parse OptionalTyping* from string. */
OptionalTyping* psOptionalTyping(const char *str)
{
  YYSTYPE result;
  yyscan_t scanner = Stella_initialize_lexer(0);
  if (!scanner) {
    fprintf(stderr, "Failed to initialize lexer.\n");
    return 0;
  }
  YY_BUFFER_STATE buf = Stella_scan_string(str, scanner);
  int error = yyparse(scanner, &result);
  Stella_delete_buffer(buf, scanner);
  Stellalex_destroy(scanner);
  if (error)
  { /* Failure */
    return 0;
  }
  else
  { /* Success */
    return result.optionaltyping_;
  }
}

/* Entrypoint: parse PatternData* from file. */
PatternData* pPatternData(FILE *inp)
{
  YYSTYPE result;
  yyscan_t scanner = Stella_initialize_lexer(inp);
  if (!scanner) {
    fprintf(stderr, "Failed to initialize lexer.\n");
    return 0;
  }
  int error = yyparse(scanner, &result);
  Stellalex_destroy(scanner);
  if (error)
  { /* Failure */
    return 0;
  }
  else
  { /* Success */
    return result.patterndata_;
  }
}

/* Entrypoint: parse PatternData* from string. */
PatternData* psPatternData(const char *str)
{
  YYSTYPE result;
  yyscan_t scanner = Stella_initialize_lexer(0);
  if (!scanner) {
    fprintf(stderr, "Failed to initialize lexer.\n");
    return 0;
  }
  YY_BUFFER_STATE buf = Stella_scan_string(str, scanner);
  int error = yyparse(scanner, &result);
  Stella_delete_buffer(buf, scanner);
  Stellalex_destroy(scanner);
  if (error)
  { /* Failure */
    return 0;
  }
  else
  { /* Success */
    return result.patterndata_;
  }
}

/* Entrypoint: parse ExprData* from file. */
ExprData* pExprData(FILE *inp)
{
  YYSTYPE result;
  yyscan_t scanner = Stella_initialize_lexer(inp);
  if (!scanner) {
    fprintf(stderr, "Failed to initialize lexer.\n");
    return 0;
  }
  int error = yyparse(scanner, &result);
  Stellalex_destroy(scanner);
  if (error)
  { /* Failure */
    return 0;
  }
  else
  { /* Success */
    return result.exprdata_;
  }
}

/* Entrypoint: parse ExprData* from string. */
ExprData* psExprData(const char *str)
{
  YYSTYPE result;
  yyscan_t scanner = Stella_initialize_lexer(0);
  if (!scanner) {
    fprintf(stderr, "Failed to initialize lexer.\n");
    return 0;
  }
  YY_BUFFER_STATE buf = Stella_scan_string(str, scanner);
  int error = yyparse(scanner, &result);
  Stella_delete_buffer(buf, scanner);
  Stellalex_destroy(scanner);
  if (error)
  { /* Failure */
    return 0;
  }
  else
  { /* Success */
    return result.exprdata_;
  }
}

/* Entrypoint: parse Pattern* from file. */
Pattern* pPattern(FILE *inp)
{
  YYSTYPE result;
  yyscan_t scanner = Stella_initialize_lexer(inp);
  if (!scanner) {
    fprintf(stderr, "Failed to initialize lexer.\n");
    return 0;
  }
  int error = yyparse(scanner, &result);
  Stellalex_destroy(scanner);
  if (error)
  { /* Failure */
    return 0;
  }
  else
  { /* Success */
    return result.pattern_;
  }
}

/* Entrypoint: parse Pattern* from string. */
Pattern* psPattern(const char *str)
{
  YYSTYPE result;
  yyscan_t scanner = Stella_initialize_lexer(0);
  if (!scanner) {
    fprintf(stderr, "Failed to initialize lexer.\n");
    return 0;
  }
  YY_BUFFER_STATE buf = Stella_scan_string(str, scanner);
  int error = yyparse(scanner, &result);
  Stella_delete_buffer(buf, scanner);
  Stellalex_destroy(scanner);
  if (error)
  { /* Failure */
    return 0;
  }
  else
  { /* Success */
    return result.pattern_;
  }
}

/* Entrypoint: parse ListPattern* from file. */
ListPattern* pListPattern(FILE *inp)
{
  YYSTYPE result;
  yyscan_t scanner = Stella_initialize_lexer(inp);
  if (!scanner) {
    fprintf(stderr, "Failed to initialize lexer.\n");
    return 0;
  }
  int error = yyparse(scanner, &result);
  Stellalex_destroy(scanner);
  if (error)
  { /* Failure */
    return 0;
  }
  else
  { /* Success */
std::reverse(result.listpattern_->begin(), result.listpattern_->end());
    return result.listpattern_;
  }
}

/* Entrypoint: parse ListPattern* from string. */
ListPattern* psListPattern(const char *str)
{
  YYSTYPE result;
  yyscan_t scanner = Stella_initialize_lexer(0);
  if (!scanner) {
    fprintf(stderr, "Failed to initialize lexer.\n");
    return 0;
  }
  YY_BUFFER_STATE buf = Stella_scan_string(str, scanner);
  int error = yyparse(scanner, &result);
  Stella_delete_buffer(buf, scanner);
  Stellalex_destroy(scanner);
  if (error)
  { /* Failure */
    return 0;
  }
  else
  { /* Success */
std::reverse(result.listpattern_->begin(), result.listpattern_->end());
    return result.listpattern_;
  }
}

/* Entrypoint: parse LabelledPattern* from file. */
LabelledPattern* pLabelledPattern(FILE *inp)
{
  YYSTYPE result;
  yyscan_t scanner = Stella_initialize_lexer(inp);
  if (!scanner) {
    fprintf(stderr, "Failed to initialize lexer.\n");
    return 0;
  }
  int error = yyparse(scanner, &result);
  Stellalex_destroy(scanner);
  if (error)
  { /* Failure */
    return 0;
  }
  else
  { /* Success */
    return result.labelledpattern_;
  }
}

/* Entrypoint: parse LabelledPattern* from string. */
LabelledPattern* psLabelledPattern(const char *str)
{
  YYSTYPE result;
  yyscan_t scanner = Stella_initialize_lexer(0);
  if (!scanner) {
    fprintf(stderr, "Failed to initialize lexer.\n");
    return 0;
  }
  YY_BUFFER_STATE buf = Stella_scan_string(str, scanner);
  int error = yyparse(scanner, &result);
  Stella_delete_buffer(buf, scanner);
  Stellalex_destroy(scanner);
  if (error)
  { /* Failure */
    return 0;
  }
  else
  { /* Success */
    return result.labelledpattern_;
  }
}

/* Entrypoint: parse ListLabelledPattern* from file. */
ListLabelledPattern* pListLabelledPattern(FILE *inp)
{
  YYSTYPE result;
  yyscan_t scanner = Stella_initialize_lexer(inp);
  if (!scanner) {
    fprintf(stderr, "Failed to initialize lexer.\n");
    return 0;
  }
  int error = yyparse(scanner, &result);
  Stellalex_destroy(scanner);
  if (error)
  { /* Failure */
    return 0;
  }
  else
  { /* Success */
std::reverse(result.listlabelledpattern_->begin(), result.listlabelledpattern_->end());
    return result.listlabelledpattern_;
  }
}

/* Entrypoint: parse ListLabelledPattern* from string. */
ListLabelledPattern* psListLabelledPattern(const char *str)
{
  YYSTYPE result;
  yyscan_t scanner = Stella_initialize_lexer(0);
  if (!scanner) {
    fprintf(stderr, "Failed to initialize lexer.\n");
    return 0;
  }
  YY_BUFFER_STATE buf = Stella_scan_string(str, scanner);
  int error = yyparse(scanner, &result);
  Stella_delete_buffer(buf, scanner);
  Stellalex_destroy(scanner);
  if (error)
  { /* Failure */
    return 0;
  }
  else
  { /* Success */
std::reverse(result.listlabelledpattern_->begin(), result.listlabelledpattern_->end());
    return result.listlabelledpattern_;
  }
}

/* Entrypoint: parse Binding* from file. */
Binding* pBinding(FILE *inp)
{
  YYSTYPE result;
  yyscan_t scanner = Stella_initialize_lexer(inp);
  if (!scanner) {
    fprintf(stderr, "Failed to initialize lexer.\n");
    return 0;
  }
  int error = yyparse(scanner, &result);
  Stellalex_destroy(scanner);
  if (error)
  { /* Failure */
    return 0;
  }
  else
  { /* Success */
    return result.binding_;
  }
}

/* Entrypoint: parse Binding* from string. */
Binding* psBinding(const char *str)
{
  YYSTYPE result;
  yyscan_t scanner = Stella_initialize_lexer(0);
  if (!scanner) {
    fprintf(stderr, "Failed to initialize lexer.\n");
    return 0;
  }
  YY_BUFFER_STATE buf = Stella_scan_string(str, scanner);
  int error = yyparse(scanner, &result);
  Stella_delete_buffer(buf, scanner);
  Stellalex_destroy(scanner);
  if (error)
  { /* Failure */
    return 0;
  }
  else
  { /* Success */
    return result.binding_;
  }
}

/* Entrypoint: parse ListBinding* from file. */
ListBinding* pListBinding(FILE *inp)
{
  YYSTYPE result;
  yyscan_t scanner = Stella_initialize_lexer(inp);
  if (!scanner) {
    fprintf(stderr, "Failed to initialize lexer.\n");
    return 0;
  }
  int error = yyparse(scanner, &result);
  Stellalex_destroy(scanner);
  if (error)
  { /* Failure */
    return 0;
  }
  else
  { /* Success */
std::reverse(result.listbinding_->begin(), result.listbinding_->end());
    return result.listbinding_;
  }
}

/* Entrypoint: parse ListBinding* from string. */
ListBinding* psListBinding(const char *str)
{
  YYSTYPE result;
  yyscan_t scanner = Stella_initialize_lexer(0);
  if (!scanner) {
    fprintf(stderr, "Failed to initialize lexer.\n");
    return 0;
  }
  YY_BUFFER_STATE buf = Stella_scan_string(str, scanner);
  int error = yyparse(scanner, &result);
  Stella_delete_buffer(buf, scanner);
  Stellalex_destroy(scanner);
  if (error)
  { /* Failure */
    return 0;
  }
  else
  { /* Success */
std::reverse(result.listbinding_->begin(), result.listbinding_->end());
    return result.listbinding_;
  }
}

/* Entrypoint: parse Expr* from file. */
Expr* pExpr1(FILE *inp)
{
  YYSTYPE result;
  yyscan_t scanner = Stella_initialize_lexer(inp);
  if (!scanner) {
    fprintf(stderr, "Failed to initialize lexer.\n");
    return 0;
  }
  int error = yyparse(scanner, &result);
  Stellalex_destroy(scanner);
  if (error)
  { /* Failure */
    return 0;
  }
  else
  { /* Success */
    return result.expr_;
  }
}

/* Entrypoint: parse Expr* from string. */
Expr* psExpr1(const char *str)
{
  YYSTYPE result;
  yyscan_t scanner = Stella_initialize_lexer(0);
  if (!scanner) {
    fprintf(stderr, "Failed to initialize lexer.\n");
    return 0;
  }
  YY_BUFFER_STATE buf = Stella_scan_string(str, scanner);
  int error = yyparse(scanner, &result);
  Stella_delete_buffer(buf, scanner);
  Stellalex_destroy(scanner);
  if (error)
  { /* Failure */
    return 0;
  }
  else
  { /* Success */
    return result.expr_;
  }
}

/* Entrypoint: parse Expr* from file. */
Expr* pExpr2(FILE *inp)
{
  YYSTYPE result;
  yyscan_t scanner = Stella_initialize_lexer(inp);
  if (!scanner) {
    fprintf(stderr, "Failed to initialize lexer.\n");
    return 0;
  }
  int error = yyparse(scanner, &result);
  Stellalex_destroy(scanner);
  if (error)
  { /* Failure */
    return 0;
  }
  else
  { /* Success */
    return result.expr_;
  }
}

/* Entrypoint: parse Expr* from string. */
Expr* psExpr2(const char *str)
{
  YYSTYPE result;
  yyscan_t scanner = Stella_initialize_lexer(0);
  if (!scanner) {
    fprintf(stderr, "Failed to initialize lexer.\n");
    return 0;
  }
  YY_BUFFER_STATE buf = Stella_scan_string(str, scanner);
  int error = yyparse(scanner, &result);
  Stella_delete_buffer(buf, scanner);
  Stellalex_destroy(scanner);
  if (error)
  { /* Failure */
    return 0;
  }
  else
  { /* Success */
    return result.expr_;
  }
}

/* Entrypoint: parse Expr* from file. */
Expr* pExpr3(FILE *inp)
{
  YYSTYPE result;
  yyscan_t scanner = Stella_initialize_lexer(inp);
  if (!scanner) {
    fprintf(stderr, "Failed to initialize lexer.\n");
    return 0;
  }
  int error = yyparse(scanner, &result);
  Stellalex_destroy(scanner);
  if (error)
  { /* Failure */
    return 0;
  }
  else
  { /* Success */
    return result.expr_;
  }
}

/* Entrypoint: parse Expr* from string. */
Expr* psExpr3(const char *str)
{
  YYSTYPE result;
  yyscan_t scanner = Stella_initialize_lexer(0);
  if (!scanner) {
    fprintf(stderr, "Failed to initialize lexer.\n");
    return 0;
  }
  YY_BUFFER_STATE buf = Stella_scan_string(str, scanner);
  int error = yyparse(scanner, &result);
  Stella_delete_buffer(buf, scanner);
  Stellalex_destroy(scanner);
  if (error)
  { /* Failure */
    return 0;
  }
  else
  { /* Success */
    return result.expr_;
  }
}

/* Entrypoint: parse Expr* from file. */
Expr* pExpr4(FILE *inp)
{
  YYSTYPE result;
  yyscan_t scanner = Stella_initialize_lexer(inp);
  if (!scanner) {
    fprintf(stderr, "Failed to initialize lexer.\n");
    return 0;
  }
  int error = yyparse(scanner, &result);
  Stellalex_destroy(scanner);
  if (error)
  { /* Failure */
    return 0;
  }
  else
  { /* Success */
    return result.expr_;
  }
}

/* Entrypoint: parse Expr* from string. */
Expr* psExpr4(const char *str)
{
  YYSTYPE result;
  yyscan_t scanner = Stella_initialize_lexer(0);
  if (!scanner) {
    fprintf(stderr, "Failed to initialize lexer.\n");
    return 0;
  }
  YY_BUFFER_STATE buf = Stella_scan_string(str, scanner);
  int error = yyparse(scanner, &result);
  Stella_delete_buffer(buf, scanner);
  Stellalex_destroy(scanner);
  if (error)
  { /* Failure */
    return 0;
  }
  else
  { /* Success */
    return result.expr_;
  }
}

/* Entrypoint: parse Expr* from file. */
Expr* pExpr5(FILE *inp)
{
  YYSTYPE result;
  yyscan_t scanner = Stella_initialize_lexer(inp);
  if (!scanner) {
    fprintf(stderr, "Failed to initialize lexer.\n");
    return 0;
  }
  int error = yyparse(scanner, &result);
  Stellalex_destroy(scanner);
  if (error)
  { /* Failure */
    return 0;
  }
  else
  { /* Success */
    return result.expr_;
  }
}

/* Entrypoint: parse Expr* from string. */
Expr* psExpr5(const char *str)
{
  YYSTYPE result;
  yyscan_t scanner = Stella_initialize_lexer(0);
  if (!scanner) {
    fprintf(stderr, "Failed to initialize lexer.\n");
    return 0;
  }
  YY_BUFFER_STATE buf = Stella_scan_string(str, scanner);
  int error = yyparse(scanner, &result);
  Stella_delete_buffer(buf, scanner);
  Stellalex_destroy(scanner);
  if (error)
  { /* Failure */
    return 0;
  }
  else
  { /* Success */
    return result.expr_;
  }
}

/* Entrypoint: parse Expr* from file. */
Expr* pExpr6(FILE *inp)
{
  YYSTYPE result;
  yyscan_t scanner = Stella_initialize_lexer(inp);
  if (!scanner) {
    fprintf(stderr, "Failed to initialize lexer.\n");
    return 0;
  }
  int error = yyparse(scanner, &result);
  Stellalex_destroy(scanner);
  if (error)
  { /* Failure */
    return 0;
  }
  else
  { /* Success */
    return result.expr_;
  }
}

/* Entrypoint: parse Expr* from string. */
Expr* psExpr6(const char *str)
{
  YYSTYPE result;
  yyscan_t scanner = Stella_initialize_lexer(0);
  if (!scanner) {
    fprintf(stderr, "Failed to initialize lexer.\n");
    return 0;
  }
  YY_BUFFER_STATE buf = Stella_scan_string(str, scanner);
  int error = yyparse(scanner, &result);
  Stella_delete_buffer(buf, scanner);
  Stellalex_destroy(scanner);
  if (error)
  { /* Failure */
    return 0;
  }
  else
  { /* Success */
    return result.expr_;
  }
}

/* Entrypoint: parse Type* from file. */
Type* pType(FILE *inp)
{
  YYSTYPE result;
  yyscan_t scanner = Stella_initialize_lexer(inp);
  if (!scanner) {
    fprintf(stderr, "Failed to initialize lexer.\n");
    return 0;
  }
  int error = yyparse(scanner, &result);
  Stellalex_destroy(scanner);
  if (error)
  { /* Failure */
    return 0;
  }
  else
  { /* Success */
    return result.type_;
  }
}

/* Entrypoint: parse Type* from string. */
Type* psType(const char *str)
{
  YYSTYPE result;
  yyscan_t scanner = Stella_initialize_lexer(0);
  if (!scanner) {
    fprintf(stderr, "Failed to initialize lexer.\n");
    return 0;
  }
  YY_BUFFER_STATE buf = Stella_scan_string(str, scanner);
  int error = yyparse(scanner, &result);
  Stella_delete_buffer(buf, scanner);
  Stellalex_destroy(scanner);
  if (error)
  { /* Failure */
    return 0;
  }
  else
  { /* Success */
    return result.type_;
  }
}

/* Entrypoint: parse Type* from file. */
Type* pType1(FILE *inp)
{
  YYSTYPE result;
  yyscan_t scanner = Stella_initialize_lexer(inp);
  if (!scanner) {
    fprintf(stderr, "Failed to initialize lexer.\n");
    return 0;
  }
  int error = yyparse(scanner, &result);
  Stellalex_destroy(scanner);
  if (error)
  { /* Failure */
    return 0;
  }
  else
  { /* Success */
    return result.type_;
  }
}

/* Entrypoint: parse Type* from string. */
Type* psType1(const char *str)
{
  YYSTYPE result;
  yyscan_t scanner = Stella_initialize_lexer(0);
  if (!scanner) {
    fprintf(stderr, "Failed to initialize lexer.\n");
    return 0;
  }
  YY_BUFFER_STATE buf = Stella_scan_string(str, scanner);
  int error = yyparse(scanner, &result);
  Stella_delete_buffer(buf, scanner);
  Stellalex_destroy(scanner);
  if (error)
  { /* Failure */
    return 0;
  }
  else
  { /* Success */
    return result.type_;
  }
}

/* Entrypoint: parse Type* from file. */
Type* pType2(FILE *inp)
{
  YYSTYPE result;
  yyscan_t scanner = Stella_initialize_lexer(inp);
  if (!scanner) {
    fprintf(stderr, "Failed to initialize lexer.\n");
    return 0;
  }
  int error = yyparse(scanner, &result);
  Stellalex_destroy(scanner);
  if (error)
  { /* Failure */
    return 0;
  }
  else
  { /* Success */
    return result.type_;
  }
}

/* Entrypoint: parse Type* from string. */
Type* psType2(const char *str)
{
  YYSTYPE result;
  yyscan_t scanner = Stella_initialize_lexer(0);
  if (!scanner) {
    fprintf(stderr, "Failed to initialize lexer.\n");
    return 0;
  }
  YY_BUFFER_STATE buf = Stella_scan_string(str, scanner);
  int error = yyparse(scanner, &result);
  Stella_delete_buffer(buf, scanner);
  Stellalex_destroy(scanner);
  if (error)
  { /* Failure */
    return 0;
  }
  else
  { /* Success */
    return result.type_;
  }
}

/* Entrypoint: parse Type* from file. */
Type* pType3(FILE *inp)
{
  YYSTYPE result;
  yyscan_t scanner = Stella_initialize_lexer(inp);
  if (!scanner) {
    fprintf(stderr, "Failed to initialize lexer.\n");
    return 0;
  }
  int error = yyparse(scanner, &result);
  Stellalex_destroy(scanner);
  if (error)
  { /* Failure */
    return 0;
  }
  else
  { /* Success */
    return result.type_;
  }
}

/* Entrypoint: parse Type* from string. */
Type* psType3(const char *str)
{
  YYSTYPE result;
  yyscan_t scanner = Stella_initialize_lexer(0);
  if (!scanner) {
    fprintf(stderr, "Failed to initialize lexer.\n");
    return 0;
  }
  YY_BUFFER_STATE buf = Stella_scan_string(str, scanner);
  int error = yyparse(scanner, &result);
  Stella_delete_buffer(buf, scanner);
  Stellalex_destroy(scanner);
  if (error)
  { /* Failure */
    return 0;
  }
  else
  { /* Success */
    return result.type_;
  }
}

/* Entrypoint: parse ListType* from file. */
ListType* pListType(FILE *inp)
{
  YYSTYPE result;
  yyscan_t scanner = Stella_initialize_lexer(inp);
  if (!scanner) {
    fprintf(stderr, "Failed to initialize lexer.\n");
    return 0;
  }
  int error = yyparse(scanner, &result);
  Stellalex_destroy(scanner);
  if (error)
  { /* Failure */
    return 0;
  }
  else
  { /* Success */
std::reverse(result.listtype_->begin(), result.listtype_->end());
    return result.listtype_;
  }
}

/* Entrypoint: parse ListType* from string. */
ListType* psListType(const char *str)
{
  YYSTYPE result;
  yyscan_t scanner = Stella_initialize_lexer(0);
  if (!scanner) {
    fprintf(stderr, "Failed to initialize lexer.\n");
    return 0;
  }
  YY_BUFFER_STATE buf = Stella_scan_string(str, scanner);
  int error = yyparse(scanner, &result);
  Stella_delete_buffer(buf, scanner);
  Stellalex_destroy(scanner);
  if (error)
  { /* Failure */
    return 0;
  }
  else
  { /* Success */
std::reverse(result.listtype_->begin(), result.listtype_->end());
    return result.listtype_;
  }
}

/* Entrypoint: parse VariantFieldType* from file. */
VariantFieldType* pVariantFieldType(FILE *inp)
{
  YYSTYPE result;
  yyscan_t scanner = Stella_initialize_lexer(inp);
  if (!scanner) {
    fprintf(stderr, "Failed to initialize lexer.\n");
    return 0;
  }
  int error = yyparse(scanner, &result);
  Stellalex_destroy(scanner);
  if (error)
  { /* Failure */
    return 0;
  }
  else
  { /* Success */
    return result.variantfieldtype_;
  }
}

/* Entrypoint: parse VariantFieldType* from string. */
VariantFieldType* psVariantFieldType(const char *str)
{
  YYSTYPE result;
  yyscan_t scanner = Stella_initialize_lexer(0);
  if (!scanner) {
    fprintf(stderr, "Failed to initialize lexer.\n");
    return 0;
  }
  YY_BUFFER_STATE buf = Stella_scan_string(str, scanner);
  int error = yyparse(scanner, &result);
  Stella_delete_buffer(buf, scanner);
  Stellalex_destroy(scanner);
  if (error)
  { /* Failure */
    return 0;
  }
  else
  { /* Success */
    return result.variantfieldtype_;
  }
}

/* Entrypoint: parse ListVariantFieldType* from file. */
ListVariantFieldType* pListVariantFieldType(FILE *inp)
{
  YYSTYPE result;
  yyscan_t scanner = Stella_initialize_lexer(inp);
  if (!scanner) {
    fprintf(stderr, "Failed to initialize lexer.\n");
    return 0;
  }
  int error = yyparse(scanner, &result);
  Stellalex_destroy(scanner);
  if (error)
  { /* Failure */
    return 0;
  }
  else
  { /* Success */
std::reverse(result.listvariantfieldtype_->begin(), result.listvariantfieldtype_->end());
    return result.listvariantfieldtype_;
  }
}

/* Entrypoint: parse ListVariantFieldType* from string. */
ListVariantFieldType* psListVariantFieldType(const char *str)
{
  YYSTYPE result;
  yyscan_t scanner = Stella_initialize_lexer(0);
  if (!scanner) {
    fprintf(stderr, "Failed to initialize lexer.\n");
    return 0;
  }
  YY_BUFFER_STATE buf = Stella_scan_string(str, scanner);
  int error = yyparse(scanner, &result);
  Stella_delete_buffer(buf, scanner);
  Stellalex_destroy(scanner);
  if (error)
  { /* Failure */
    return 0;
  }
  else
  { /* Success */
std::reverse(result.listvariantfieldtype_->begin(), result.listvariantfieldtype_->end());
    return result.listvariantfieldtype_;
  }
}

/* Entrypoint: parse RecordFieldType* from file. */
RecordFieldType* pRecordFieldType(FILE *inp)
{
  YYSTYPE result;
  yyscan_t scanner = Stella_initialize_lexer(inp);
  if (!scanner) {
    fprintf(stderr, "Failed to initialize lexer.\n");
    return 0;
  }
  int error = yyparse(scanner, &result);
  Stellalex_destroy(scanner);
  if (error)
  { /* Failure */
    return 0;
  }
  else
  { /* Success */
    return result.recordfieldtype_;
  }
}

/* Entrypoint: parse RecordFieldType* from string. */
RecordFieldType* psRecordFieldType(const char *str)
{
  YYSTYPE result;
  yyscan_t scanner = Stella_initialize_lexer(0);
  if (!scanner) {
    fprintf(stderr, "Failed to initialize lexer.\n");
    return 0;
  }
  YY_BUFFER_STATE buf = Stella_scan_string(str, scanner);
  int error = yyparse(scanner, &result);
  Stella_delete_buffer(buf, scanner);
  Stellalex_destroy(scanner);
  if (error)
  { /* Failure */
    return 0;
  }
  else
  { /* Success */
    return result.recordfieldtype_;
  }
}

/* Entrypoint: parse ListRecordFieldType* from file. */
ListRecordFieldType* pListRecordFieldType(FILE *inp)
{
  YYSTYPE result;
  yyscan_t scanner = Stella_initialize_lexer(inp);
  if (!scanner) {
    fprintf(stderr, "Failed to initialize lexer.\n");
    return 0;
  }
  int error = yyparse(scanner, &result);
  Stellalex_destroy(scanner);
  if (error)
  { /* Failure */
    return 0;
  }
  else
  { /* Success */
std::reverse(result.listrecordfieldtype_->begin(), result.listrecordfieldtype_->end());
    return result.listrecordfieldtype_;
  }
}

/* Entrypoint: parse ListRecordFieldType* from string. */
ListRecordFieldType* psListRecordFieldType(const char *str)
{
  YYSTYPE result;
  yyscan_t scanner = Stella_initialize_lexer(0);
  if (!scanner) {
    fprintf(stderr, "Failed to initialize lexer.\n");
    return 0;
  }
  YY_BUFFER_STATE buf = Stella_scan_string(str, scanner);
  int error = yyparse(scanner, &result);
  Stella_delete_buffer(buf, scanner);
  Stellalex_destroy(scanner);
  if (error)
  { /* Failure */
    return 0;
  }
  else
  { /* Success */
std::reverse(result.listrecordfieldtype_->begin(), result.listrecordfieldtype_->end());
    return result.listrecordfieldtype_;
  }
}

/* Entrypoint: parse Typing* from file. */
Typing* pTyping(FILE *inp)
{
  YYSTYPE result;
  yyscan_t scanner = Stella_initialize_lexer(inp);
  if (!scanner) {
    fprintf(stderr, "Failed to initialize lexer.\n");
    return 0;
  }
  int error = yyparse(scanner, &result);
  Stellalex_destroy(scanner);
  if (error)
  { /* Failure */
    return 0;
  }
  else
  { /* Success */
    return result.typing_;
  }
}

/* Entrypoint: parse Typing* from string. */
Typing* psTyping(const char *str)
{
  YYSTYPE result;
  yyscan_t scanner = Stella_initialize_lexer(0);
  if (!scanner) {
    fprintf(stderr, "Failed to initialize lexer.\n");
    return 0;
  }
  YY_BUFFER_STATE buf = Stella_scan_string(str, scanner);
  int error = yyparse(scanner, &result);
  Stella_delete_buffer(buf, scanner);
  Stellalex_destroy(scanner);
  if (error)
  { /* Failure */
    return 0;
  }
  else
  { /* Success */
    return result.typing_;
  }
}


}
