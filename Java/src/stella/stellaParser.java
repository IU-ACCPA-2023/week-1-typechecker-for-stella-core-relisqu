// Generated from stella/stellaParser.g4 by ANTLR 4.9.3
package stella;
import org.antlr.v4.runtime.atn.*;
import org.antlr.v4.runtime.dfa.DFA;
import org.antlr.v4.runtime.*;
import org.antlr.v4.runtime.misc.*;
import org.antlr.v4.runtime.tree.*;
import java.util.List;
import java.util.Iterator;
import java.util.ArrayList;

@SuppressWarnings({"all", "warnings", "unchecked", "unused", "cast"})
public class stellaParser extends Parser {
	static { RuntimeMetaData.checkVersion("4.9.3", RuntimeMetaData.VERSION); }

	protected static final DFA[] _decisionToDFA;
	protected static final PredictionContextCache _sharedContextCache =
		new PredictionContextCache();
	public static final int
		Surrogate_id_SYMB_0=1, Surrogate_id_SYMB_1=2, Surrogate_id_SYMB_2=3, Surrogate_id_SYMB_3=4, 
		Surrogate_id_SYMB_4=5, Surrogate_id_SYMB_5=6, Surrogate_id_SYMB_6=7, Surrogate_id_SYMB_7=8, 
		Surrogate_id_SYMB_8=9, Surrogate_id_SYMB_9=10, Surrogate_id_SYMB_10=11, 
		Surrogate_id_SYMB_11=12, Surrogate_id_SYMB_12=13, Surrogate_id_SYMB_13=14, 
		Surrogate_id_SYMB_14=15, Surrogate_id_SYMB_15=16, Surrogate_id_SYMB_16=17, 
		Surrogate_id_SYMB_17=18, Surrogate_id_SYMB_18=19, Surrogate_id_SYMB_19=20, 
		Surrogate_id_SYMB_20=21, Surrogate_id_SYMB_21=22, Surrogate_id_SYMB_22=23, 
		Surrogate_id_SYMB_23=24, Surrogate_id_SYMB_24=25, Surrogate_id_SYMB_25=26, 
		Surrogate_id_SYMB_26=27, Surrogate_id_SYMB_27=28, Surrogate_id_SYMB_28=29, 
		Surrogate_id_SYMB_29=30, Surrogate_id_SYMB_30=31, Surrogate_id_SYMB_31=32, 
		Surrogate_id_SYMB_32=33, Surrogate_id_SYMB_33=34, Surrogate_id_SYMB_34=35, 
		Surrogate_id_SYMB_35=36, Surrogate_id_SYMB_36=37, Surrogate_id_SYMB_37=38, 
		Surrogate_id_SYMB_38=39, Surrogate_id_SYMB_39=40, Surrogate_id_SYMB_40=41, 
		Surrogate_id_SYMB_41=42, Surrogate_id_SYMB_42=43, Surrogate_id_SYMB_43=44, 
		Surrogate_id_SYMB_44=45, Surrogate_id_SYMB_45=46, Surrogate_id_SYMB_46=47, 
		Surrogate_id_SYMB_47=48, Surrogate_id_SYMB_48=49, Surrogate_id_SYMB_49=50, 
		Surrogate_id_SYMB_50=51, Surrogate_id_SYMB_51=52, Surrogate_id_SYMB_52=53, 
		Surrogate_id_SYMB_53=54, Surrogate_id_SYMB_54=55, Surrogate_id_SYMB_55=56, 
		Surrogate_id_SYMB_56=57, Surrogate_id_SYMB_57=58, Surrogate_id_SYMB_58=59, 
		Surrogate_id_SYMB_59=60, COMMENT_antlr_builtin=61, MULTICOMMENT_antlr_builtin=62, 
		StellaIdent=63, ExtensionName=64, INTEGER=65, WS=66, ErrorToken=67;
	public static final int
		RULE_start_Program = 0, RULE_start_LanguageDecl = 1, RULE_start_Extension = 2, 
		RULE_start_ListExtensionName = 3, RULE_start_ListExtension = 4, RULE_start_Decl = 5, 
		RULE_start_ListDecl = 6, RULE_start_LocalDecl = 7, RULE_start_ListLocalDecl = 8, 
		RULE_start_Annotation = 9, RULE_start_ListAnnotation = 10, RULE_start_ParamDecl = 11, 
		RULE_start_ListParamDecl = 12, RULE_start_ReturnType = 13, RULE_start_ThrowType = 14, 
		RULE_start_Expr = 15, RULE_start_ListExpr = 16, RULE_start_MatchCase = 17, 
		RULE_start_ListMatchCase = 18, RULE_start_Pattern = 19, RULE_start_ListPattern = 20, 
		RULE_start_LabelledPattern = 21, RULE_start_ListLabelledPattern = 22, 
		RULE_start_Binding = 23, RULE_start_ListBinding = 24, RULE_start_Expr0 = 25, 
		RULE_start_Expr1 = 26, RULE_start_Expr2 = 27, RULE_start_Expr3 = 28, RULE_start_Expr4 = 29, 
		RULE_start_Expr5 = 30, RULE_start_Type = 31, RULE_start_Type1 = 32, RULE_start_Type2 = 33, 
		RULE_start_ListType = 34, RULE_start_FieldType = 35, RULE_start_ListFieldType = 36, 
		RULE_start_Typing = 37, RULE_program = 38, RULE_languageDecl = 39, RULE_extension = 40, 
		RULE_listExtensionName = 41, RULE_listExtension = 42, RULE_decl = 43, 
		RULE_listDecl = 44, RULE_localDecl = 45, RULE_listLocalDecl = 46, RULE_annotation = 47, 
		RULE_listAnnotation = 48, RULE_paramDecl = 49, RULE_listParamDecl = 50, 
		RULE_returnType = 51, RULE_throwType = 52, RULE_expr = 53, RULE_listExpr = 54, 
		RULE_matchCase = 55, RULE_listMatchCase = 56, RULE_pattern = 57, RULE_listPattern = 58, 
		RULE_labelledPattern = 59, RULE_listLabelledPattern = 60, RULE_binding = 61, 
		RULE_listBinding = 62, RULE_expr0 = 63, RULE_expr1 = 64, RULE_expr2 = 65, 
		RULE_expr3 = 66, RULE_expr4 = 67, RULE_expr5 = 68, RULE_type = 69, RULE_type1 = 70, 
		RULE_type2 = 71, RULE_listType = 72, RULE_fieldType = 73, RULE_listFieldType = 74, 
		RULE_typing = 75;
	private static String[] makeRuleNames() {
		return new String[] {
			"start_Program", "start_LanguageDecl", "start_Extension", "start_ListExtensionName", 
			"start_ListExtension", "start_Decl", "start_ListDecl", "start_LocalDecl", 
			"start_ListLocalDecl", "start_Annotation", "start_ListAnnotation", "start_ParamDecl", 
			"start_ListParamDecl", "start_ReturnType", "start_ThrowType", "start_Expr", 
			"start_ListExpr", "start_MatchCase", "start_ListMatchCase", "start_Pattern", 
			"start_ListPattern", "start_LabelledPattern", "start_ListLabelledPattern", 
			"start_Binding", "start_ListBinding", "start_Expr0", "start_Expr1", "start_Expr2", 
			"start_Expr3", "start_Expr4", "start_Expr5", "start_Type", "start_Type1", 
			"start_Type2", "start_ListType", "start_FieldType", "start_ListFieldType", 
			"start_Typing", "program", "languageDecl", "extension", "listExtensionName", 
			"listExtension", "decl", "listDecl", "localDecl", "listLocalDecl", "annotation", 
			"listAnnotation", "paramDecl", "listParamDecl", "returnType", "throwType", 
			"expr", "listExpr", "matchCase", "listMatchCase", "pattern", "listPattern", 
			"labelledPattern", "listLabelledPattern", "binding", "listBinding", "expr0", 
			"expr1", "expr2", "expr3", "expr4", "expr5", "type", "type1", "type2", 
			"listType", "fieldType", "listFieldType", "typing"
		};
	}
	public static final String[] ruleNames = makeRuleNames();

	private static String[] makeLiteralNames() {
		return new String[] {
			null, "';'", "','", "'('", "')'", "'{'", "'}'", "'='", "':'", "'->'", 
			"'=>'", "'<'", "'>'", "'['", "']'", "'<='", "'>='", "'=='", "'!='", "'+'", 
			"'*'", "'List::head'", "'List::isempty'", "'List::tail'", "'Nat::pred'", 
			"'Nat::iszero'", "'Nat::rec'", "'.'", "'Bool'", "'Nat'", "'Unit'", "'and'", 
			"'as'", "'cons'", "'core'", "'else'", "'extend'", "'false'", "'fix'", 
			"'fn'", "'fold'", "'if'", "'in'", "'inline'", "'language'", "'let'", 
			"'match'", "'not'", "'or'", "'record'", "'return'", "'struct'", "'succ'", 
			"'then'", "'throws'", "'true'", "'type'", "'unfold'", "'variant'", "'with'", 
			"'\u00B5'"
		};
	}
	private static final String[] _LITERAL_NAMES = makeLiteralNames();
	private static String[] makeSymbolicNames() {
		return new String[] {
			null, "Surrogate_id_SYMB_0", "Surrogate_id_SYMB_1", "Surrogate_id_SYMB_2", 
			"Surrogate_id_SYMB_3", "Surrogate_id_SYMB_4", "Surrogate_id_SYMB_5", 
			"Surrogate_id_SYMB_6", "Surrogate_id_SYMB_7", "Surrogate_id_SYMB_8", 
			"Surrogate_id_SYMB_9", "Surrogate_id_SYMB_10", "Surrogate_id_SYMB_11", 
			"Surrogate_id_SYMB_12", "Surrogate_id_SYMB_13", "Surrogate_id_SYMB_14", 
			"Surrogate_id_SYMB_15", "Surrogate_id_SYMB_16", "Surrogate_id_SYMB_17", 
			"Surrogate_id_SYMB_18", "Surrogate_id_SYMB_19", "Surrogate_id_SYMB_20", 
			"Surrogate_id_SYMB_21", "Surrogate_id_SYMB_22", "Surrogate_id_SYMB_23", 
			"Surrogate_id_SYMB_24", "Surrogate_id_SYMB_25", "Surrogate_id_SYMB_26", 
			"Surrogate_id_SYMB_27", "Surrogate_id_SYMB_28", "Surrogate_id_SYMB_29", 
			"Surrogate_id_SYMB_30", "Surrogate_id_SYMB_31", "Surrogate_id_SYMB_32", 
			"Surrogate_id_SYMB_33", "Surrogate_id_SYMB_34", "Surrogate_id_SYMB_35", 
			"Surrogate_id_SYMB_36", "Surrogate_id_SYMB_37", "Surrogate_id_SYMB_38", 
			"Surrogate_id_SYMB_39", "Surrogate_id_SYMB_40", "Surrogate_id_SYMB_41", 
			"Surrogate_id_SYMB_42", "Surrogate_id_SYMB_43", "Surrogate_id_SYMB_44", 
			"Surrogate_id_SYMB_45", "Surrogate_id_SYMB_46", "Surrogate_id_SYMB_47", 
			"Surrogate_id_SYMB_48", "Surrogate_id_SYMB_49", "Surrogate_id_SYMB_50", 
			"Surrogate_id_SYMB_51", "Surrogate_id_SYMB_52", "Surrogate_id_SYMB_53", 
			"Surrogate_id_SYMB_54", "Surrogate_id_SYMB_55", "Surrogate_id_SYMB_56", 
			"Surrogate_id_SYMB_57", "Surrogate_id_SYMB_58", "Surrogate_id_SYMB_59", 
			"COMMENT_antlr_builtin", "MULTICOMMENT_antlr_builtin", "StellaIdent", 
			"ExtensionName", "INTEGER", "WS", "ErrorToken"
		};
	}
	private static final String[] _SYMBOLIC_NAMES = makeSymbolicNames();
	public static final Vocabulary VOCABULARY = new VocabularyImpl(_LITERAL_NAMES, _SYMBOLIC_NAMES);

	/**
	 * @deprecated Use {@link #VOCABULARY} instead.
	 */
	@Deprecated
	public static final String[] tokenNames;
	static {
		tokenNames = new String[_SYMBOLIC_NAMES.length];
		for (int i = 0; i < tokenNames.length; i++) {
			tokenNames[i] = VOCABULARY.getLiteralName(i);
			if (tokenNames[i] == null) {
				tokenNames[i] = VOCABULARY.getSymbolicName(i);
			}

			if (tokenNames[i] == null) {
				tokenNames[i] = "<INVALID>";
			}
		}
	}

	@Override
	@Deprecated
	public String[] getTokenNames() {
		return tokenNames;
	}

	@Override

	public Vocabulary getVocabulary() {
		return VOCABULARY;
	}

	@Override
	public String getGrammarFileName() { return "stellaParser.g4"; }

	@Override
	public String[] getRuleNames() { return ruleNames; }

	@Override
	public String getSerializedATN() { return _serializedATN; }

	@Override
	public ATN getATN() { return _ATN; }

	public stellaParser(TokenStream input) {
		super(input);
		_interp = new ParserATNSimulator(this,_ATN,_decisionToDFA,_sharedContextCache);
	}

	public static class Start_ProgramContext extends ParserRuleContext {
		public stella.Absyn.Program result;
		public ProgramContext x;
		public TerminalNode EOF() { return getToken(stellaParser.EOF, 0); }
		public ProgramContext program() {
			return getRuleContext(ProgramContext.class,0);
		}
		public Start_ProgramContext(ParserRuleContext parent, int invokingState) {
			super(parent, invokingState);
		}
		@Override public int getRuleIndex() { return RULE_start_Program; }
		@Override
		public void enterRule(ParseTreeListener listener) {
			if ( listener instanceof stellaParserListener ) ((stellaParserListener)listener).enterStart_Program(this);
		}
		@Override
		public void exitRule(ParseTreeListener listener) {
			if ( listener instanceof stellaParserListener ) ((stellaParserListener)listener).exitStart_Program(this);
		}
	}

	public final Start_ProgramContext start_Program() throws RecognitionException {
		Start_ProgramContext _localctx = new Start_ProgramContext(_ctx, getState());
		enterRule(_localctx, 0, RULE_start_Program);
		try {
			enterOuterAlt(_localctx, 1);
			{
			setState(152);
			((Start_ProgramContext)_localctx).x = program();
			setState(153);
			match(EOF);
			 ((Start_ProgramContext)_localctx).result =  ((Start_ProgramContext)_localctx).x.result; 
			}
		}
		catch (RecognitionException re) {
			_localctx.exception = re;
			_errHandler.reportError(this, re);
			_errHandler.recover(this, re);
		}
		finally {
			exitRule();
		}
		return _localctx;
	}

	public static class Start_LanguageDeclContext extends ParserRuleContext {
		public stella.Absyn.LanguageDecl result;
		public LanguageDeclContext x;
		public TerminalNode EOF() { return getToken(stellaParser.EOF, 0); }
		public LanguageDeclContext languageDecl() {
			return getRuleContext(LanguageDeclContext.class,0);
		}
		public Start_LanguageDeclContext(ParserRuleContext parent, int invokingState) {
			super(parent, invokingState);
		}
		@Override public int getRuleIndex() { return RULE_start_LanguageDecl; }
		@Override
		public void enterRule(ParseTreeListener listener) {
			if ( listener instanceof stellaParserListener ) ((stellaParserListener)listener).enterStart_LanguageDecl(this);
		}
		@Override
		public void exitRule(ParseTreeListener listener) {
			if ( listener instanceof stellaParserListener ) ((stellaParserListener)listener).exitStart_LanguageDecl(this);
		}
	}

	public final Start_LanguageDeclContext start_LanguageDecl() throws RecognitionException {
		Start_LanguageDeclContext _localctx = new Start_LanguageDeclContext(_ctx, getState());
		enterRule(_localctx, 2, RULE_start_LanguageDecl);
		try {
			enterOuterAlt(_localctx, 1);
			{
			setState(156);
			((Start_LanguageDeclContext)_localctx).x = languageDecl();
			setState(157);
			match(EOF);
			 ((Start_LanguageDeclContext)_localctx).result =  ((Start_LanguageDeclContext)_localctx).x.result; 
			}
		}
		catch (RecognitionException re) {
			_localctx.exception = re;
			_errHandler.reportError(this, re);
			_errHandler.recover(this, re);
		}
		finally {
			exitRule();
		}
		return _localctx;
	}

	public static class Start_ExtensionContext extends ParserRuleContext {
		public stella.Absyn.Extension result;
		public ExtensionContext x;
		public TerminalNode EOF() { return getToken(stellaParser.EOF, 0); }
		public ExtensionContext extension() {
			return getRuleContext(ExtensionContext.class,0);
		}
		public Start_ExtensionContext(ParserRuleContext parent, int invokingState) {
			super(parent, invokingState);
		}
		@Override public int getRuleIndex() { return RULE_start_Extension; }
		@Override
		public void enterRule(ParseTreeListener listener) {
			if ( listener instanceof stellaParserListener ) ((stellaParserListener)listener).enterStart_Extension(this);
		}
		@Override
		public void exitRule(ParseTreeListener listener) {
			if ( listener instanceof stellaParserListener ) ((stellaParserListener)listener).exitStart_Extension(this);
		}
	}

	public final Start_ExtensionContext start_Extension() throws RecognitionException {
		Start_ExtensionContext _localctx = new Start_ExtensionContext(_ctx, getState());
		enterRule(_localctx, 4, RULE_start_Extension);
		try {
			enterOuterAlt(_localctx, 1);
			{
			setState(160);
			((Start_ExtensionContext)_localctx).x = extension();
			setState(161);
			match(EOF);
			 ((Start_ExtensionContext)_localctx).result =  ((Start_ExtensionContext)_localctx).x.result; 
			}
		}
		catch (RecognitionException re) {
			_localctx.exception = re;
			_errHandler.reportError(this, re);
			_errHandler.recover(this, re);
		}
		finally {
			exitRule();
		}
		return _localctx;
	}

	public static class Start_ListExtensionNameContext extends ParserRuleContext {
		public stella.Absyn.ListExtensionName result;
		public ListExtensionNameContext x;
		public TerminalNode EOF() { return getToken(stellaParser.EOF, 0); }
		public ListExtensionNameContext listExtensionName() {
			return getRuleContext(ListExtensionNameContext.class,0);
		}
		public Start_ListExtensionNameContext(ParserRuleContext parent, int invokingState) {
			super(parent, invokingState);
		}
		@Override public int getRuleIndex() { return RULE_start_ListExtensionName; }
		@Override
		public void enterRule(ParseTreeListener listener) {
			if ( listener instanceof stellaParserListener ) ((stellaParserListener)listener).enterStart_ListExtensionName(this);
		}
		@Override
		public void exitRule(ParseTreeListener listener) {
			if ( listener instanceof stellaParserListener ) ((stellaParserListener)listener).exitStart_ListExtensionName(this);
		}
	}

	public final Start_ListExtensionNameContext start_ListExtensionName() throws RecognitionException {
		Start_ListExtensionNameContext _localctx = new Start_ListExtensionNameContext(_ctx, getState());
		enterRule(_localctx, 6, RULE_start_ListExtensionName);
		try {
			enterOuterAlt(_localctx, 1);
			{
			setState(164);
			((Start_ListExtensionNameContext)_localctx).x = listExtensionName();
			setState(165);
			match(EOF);
			 ((Start_ListExtensionNameContext)_localctx).result =  ((Start_ListExtensionNameContext)_localctx).x.result; 
			}
		}
		catch (RecognitionException re) {
			_localctx.exception = re;
			_errHandler.reportError(this, re);
			_errHandler.recover(this, re);
		}
		finally {
			exitRule();
		}
		return _localctx;
	}

	public static class Start_ListExtensionContext extends ParserRuleContext {
		public stella.Absyn.ListExtension result;
		public ListExtensionContext x;
		public TerminalNode EOF() { return getToken(stellaParser.EOF, 0); }
		public ListExtensionContext listExtension() {
			return getRuleContext(ListExtensionContext.class,0);
		}
		public Start_ListExtensionContext(ParserRuleContext parent, int invokingState) {
			super(parent, invokingState);
		}
		@Override public int getRuleIndex() { return RULE_start_ListExtension; }
		@Override
		public void enterRule(ParseTreeListener listener) {
			if ( listener instanceof stellaParserListener ) ((stellaParserListener)listener).enterStart_ListExtension(this);
		}
		@Override
		public void exitRule(ParseTreeListener listener) {
			if ( listener instanceof stellaParserListener ) ((stellaParserListener)listener).exitStart_ListExtension(this);
		}
	}

	public final Start_ListExtensionContext start_ListExtension() throws RecognitionException {
		Start_ListExtensionContext _localctx = new Start_ListExtensionContext(_ctx, getState());
		enterRule(_localctx, 8, RULE_start_ListExtension);
		try {
			enterOuterAlt(_localctx, 1);
			{
			setState(168);
			((Start_ListExtensionContext)_localctx).x = listExtension(0);
			setState(169);
			match(EOF);
			 ((Start_ListExtensionContext)_localctx).result =  ((Start_ListExtensionContext)_localctx).x.result; 
			}
		}
		catch (RecognitionException re) {
			_localctx.exception = re;
			_errHandler.reportError(this, re);
			_errHandler.recover(this, re);
		}
		finally {
			exitRule();
		}
		return _localctx;
	}

	public static class Start_DeclContext extends ParserRuleContext {
		public stella.Absyn.Decl result;
		public DeclContext x;
		public TerminalNode EOF() { return getToken(stellaParser.EOF, 0); }
		public DeclContext decl() {
			return getRuleContext(DeclContext.class,0);
		}
		public Start_DeclContext(ParserRuleContext parent, int invokingState) {
			super(parent, invokingState);
		}
		@Override public int getRuleIndex() { return RULE_start_Decl; }
		@Override
		public void enterRule(ParseTreeListener listener) {
			if ( listener instanceof stellaParserListener ) ((stellaParserListener)listener).enterStart_Decl(this);
		}
		@Override
		public void exitRule(ParseTreeListener listener) {
			if ( listener instanceof stellaParserListener ) ((stellaParserListener)listener).exitStart_Decl(this);
		}
	}

	public final Start_DeclContext start_Decl() throws RecognitionException {
		Start_DeclContext _localctx = new Start_DeclContext(_ctx, getState());
		enterRule(_localctx, 10, RULE_start_Decl);
		try {
			enterOuterAlt(_localctx, 1);
			{
			setState(172);
			((Start_DeclContext)_localctx).x = decl();
			setState(173);
			match(EOF);
			 ((Start_DeclContext)_localctx).result =  ((Start_DeclContext)_localctx).x.result; 
			}
		}
		catch (RecognitionException re) {
			_localctx.exception = re;
			_errHandler.reportError(this, re);
			_errHandler.recover(this, re);
		}
		finally {
			exitRule();
		}
		return _localctx;
	}

	public static class Start_ListDeclContext extends ParserRuleContext {
		public stella.Absyn.ListDecl result;
		public ListDeclContext x;
		public TerminalNode EOF() { return getToken(stellaParser.EOF, 0); }
		public ListDeclContext listDecl() {
			return getRuleContext(ListDeclContext.class,0);
		}
		public Start_ListDeclContext(ParserRuleContext parent, int invokingState) {
			super(parent, invokingState);
		}
		@Override public int getRuleIndex() { return RULE_start_ListDecl; }
		@Override
		public void enterRule(ParseTreeListener listener) {
			if ( listener instanceof stellaParserListener ) ((stellaParserListener)listener).enterStart_ListDecl(this);
		}
		@Override
		public void exitRule(ParseTreeListener listener) {
			if ( listener instanceof stellaParserListener ) ((stellaParserListener)listener).exitStart_ListDecl(this);
		}
	}

	public final Start_ListDeclContext start_ListDecl() throws RecognitionException {
		Start_ListDeclContext _localctx = new Start_ListDeclContext(_ctx, getState());
		enterRule(_localctx, 12, RULE_start_ListDecl);
		try {
			enterOuterAlt(_localctx, 1);
			{
			setState(176);
			((Start_ListDeclContext)_localctx).x = listDecl(0);
			setState(177);
			match(EOF);
			 ((Start_ListDeclContext)_localctx).result =  ((Start_ListDeclContext)_localctx).x.result; 
			}
		}
		catch (RecognitionException re) {
			_localctx.exception = re;
			_errHandler.reportError(this, re);
			_errHandler.recover(this, re);
		}
		finally {
			exitRule();
		}
		return _localctx;
	}

	public static class Start_LocalDeclContext extends ParserRuleContext {
		public stella.Absyn.LocalDecl result;
		public LocalDeclContext x;
		public TerminalNode EOF() { return getToken(stellaParser.EOF, 0); }
		public LocalDeclContext localDecl() {
			return getRuleContext(LocalDeclContext.class,0);
		}
		public Start_LocalDeclContext(ParserRuleContext parent, int invokingState) {
			super(parent, invokingState);
		}
		@Override public int getRuleIndex() { return RULE_start_LocalDecl; }
		@Override
		public void enterRule(ParseTreeListener listener) {
			if ( listener instanceof stellaParserListener ) ((stellaParserListener)listener).enterStart_LocalDecl(this);
		}
		@Override
		public void exitRule(ParseTreeListener listener) {
			if ( listener instanceof stellaParserListener ) ((stellaParserListener)listener).exitStart_LocalDecl(this);
		}
	}

	public final Start_LocalDeclContext start_LocalDecl() throws RecognitionException {
		Start_LocalDeclContext _localctx = new Start_LocalDeclContext(_ctx, getState());
		enterRule(_localctx, 14, RULE_start_LocalDecl);
		try {
			enterOuterAlt(_localctx, 1);
			{
			setState(180);
			((Start_LocalDeclContext)_localctx).x = localDecl();
			setState(181);
			match(EOF);
			 ((Start_LocalDeclContext)_localctx).result =  ((Start_LocalDeclContext)_localctx).x.result; 
			}
		}
		catch (RecognitionException re) {
			_localctx.exception = re;
			_errHandler.reportError(this, re);
			_errHandler.recover(this, re);
		}
		finally {
			exitRule();
		}
		return _localctx;
	}

	public static class Start_ListLocalDeclContext extends ParserRuleContext {
		public stella.Absyn.ListLocalDecl result;
		public ListLocalDeclContext x;
		public TerminalNode EOF() { return getToken(stellaParser.EOF, 0); }
		public ListLocalDeclContext listLocalDecl() {
			return getRuleContext(ListLocalDeclContext.class,0);
		}
		public Start_ListLocalDeclContext(ParserRuleContext parent, int invokingState) {
			super(parent, invokingState);
		}
		@Override public int getRuleIndex() { return RULE_start_ListLocalDecl; }
		@Override
		public void enterRule(ParseTreeListener listener) {
			if ( listener instanceof stellaParserListener ) ((stellaParserListener)listener).enterStart_ListLocalDecl(this);
		}
		@Override
		public void exitRule(ParseTreeListener listener) {
			if ( listener instanceof stellaParserListener ) ((stellaParserListener)listener).exitStart_ListLocalDecl(this);
		}
	}

	public final Start_ListLocalDeclContext start_ListLocalDecl() throws RecognitionException {
		Start_ListLocalDeclContext _localctx = new Start_ListLocalDeclContext(_ctx, getState());
		enterRule(_localctx, 16, RULE_start_ListLocalDecl);
		try {
			enterOuterAlt(_localctx, 1);
			{
			setState(184);
			((Start_ListLocalDeclContext)_localctx).x = listLocalDecl(0);
			setState(185);
			match(EOF);
			 ((Start_ListLocalDeclContext)_localctx).result =  ((Start_ListLocalDeclContext)_localctx).x.result; 
			}
		}
		catch (RecognitionException re) {
			_localctx.exception = re;
			_errHandler.reportError(this, re);
			_errHandler.recover(this, re);
		}
		finally {
			exitRule();
		}
		return _localctx;
	}

	public static class Start_AnnotationContext extends ParserRuleContext {
		public stella.Absyn.Annotation result;
		public AnnotationContext x;
		public TerminalNode EOF() { return getToken(stellaParser.EOF, 0); }
		public AnnotationContext annotation() {
			return getRuleContext(AnnotationContext.class,0);
		}
		public Start_AnnotationContext(ParserRuleContext parent, int invokingState) {
			super(parent, invokingState);
		}
		@Override public int getRuleIndex() { return RULE_start_Annotation; }
		@Override
		public void enterRule(ParseTreeListener listener) {
			if ( listener instanceof stellaParserListener ) ((stellaParserListener)listener).enterStart_Annotation(this);
		}
		@Override
		public void exitRule(ParseTreeListener listener) {
			if ( listener instanceof stellaParserListener ) ((stellaParserListener)listener).exitStart_Annotation(this);
		}
	}

	public final Start_AnnotationContext start_Annotation() throws RecognitionException {
		Start_AnnotationContext _localctx = new Start_AnnotationContext(_ctx, getState());
		enterRule(_localctx, 18, RULE_start_Annotation);
		try {
			enterOuterAlt(_localctx, 1);
			{
			setState(188);
			((Start_AnnotationContext)_localctx).x = annotation();
			setState(189);
			match(EOF);
			 ((Start_AnnotationContext)_localctx).result =  ((Start_AnnotationContext)_localctx).x.result; 
			}
		}
		catch (RecognitionException re) {
			_localctx.exception = re;
			_errHandler.reportError(this, re);
			_errHandler.recover(this, re);
		}
		finally {
			exitRule();
		}
		return _localctx;
	}

	public static class Start_ListAnnotationContext extends ParserRuleContext {
		public stella.Absyn.ListAnnotation result;
		public ListAnnotationContext x;
		public TerminalNode EOF() { return getToken(stellaParser.EOF, 0); }
		public ListAnnotationContext listAnnotation() {
			return getRuleContext(ListAnnotationContext.class,0);
		}
		public Start_ListAnnotationContext(ParserRuleContext parent, int invokingState) {
			super(parent, invokingState);
		}
		@Override public int getRuleIndex() { return RULE_start_ListAnnotation; }
		@Override
		public void enterRule(ParseTreeListener listener) {
			if ( listener instanceof stellaParserListener ) ((stellaParserListener)listener).enterStart_ListAnnotation(this);
		}
		@Override
		public void exitRule(ParseTreeListener listener) {
			if ( listener instanceof stellaParserListener ) ((stellaParserListener)listener).exitStart_ListAnnotation(this);
		}
	}

	public final Start_ListAnnotationContext start_ListAnnotation() throws RecognitionException {
		Start_ListAnnotationContext _localctx = new Start_ListAnnotationContext(_ctx, getState());
		enterRule(_localctx, 20, RULE_start_ListAnnotation);
		try {
			enterOuterAlt(_localctx, 1);
			{
			setState(192);
			((Start_ListAnnotationContext)_localctx).x = listAnnotation(0);
			setState(193);
			match(EOF);
			 ((Start_ListAnnotationContext)_localctx).result =  ((Start_ListAnnotationContext)_localctx).x.result; 
			}
		}
		catch (RecognitionException re) {
			_localctx.exception = re;
			_errHandler.reportError(this, re);
			_errHandler.recover(this, re);
		}
		finally {
			exitRule();
		}
		return _localctx;
	}

	public static class Start_ParamDeclContext extends ParserRuleContext {
		public stella.Absyn.ParamDecl result;
		public ParamDeclContext x;
		public TerminalNode EOF() { return getToken(stellaParser.EOF, 0); }
		public ParamDeclContext paramDecl() {
			return getRuleContext(ParamDeclContext.class,0);
		}
		public Start_ParamDeclContext(ParserRuleContext parent, int invokingState) {
			super(parent, invokingState);
		}
		@Override public int getRuleIndex() { return RULE_start_ParamDecl; }
		@Override
		public void enterRule(ParseTreeListener listener) {
			if ( listener instanceof stellaParserListener ) ((stellaParserListener)listener).enterStart_ParamDecl(this);
		}
		@Override
		public void exitRule(ParseTreeListener listener) {
			if ( listener instanceof stellaParserListener ) ((stellaParserListener)listener).exitStart_ParamDecl(this);
		}
	}

	public final Start_ParamDeclContext start_ParamDecl() throws RecognitionException {
		Start_ParamDeclContext _localctx = new Start_ParamDeclContext(_ctx, getState());
		enterRule(_localctx, 22, RULE_start_ParamDecl);
		try {
			enterOuterAlt(_localctx, 1);
			{
			setState(196);
			((Start_ParamDeclContext)_localctx).x = paramDecl();
			setState(197);
			match(EOF);
			 ((Start_ParamDeclContext)_localctx).result =  ((Start_ParamDeclContext)_localctx).x.result; 
			}
		}
		catch (RecognitionException re) {
			_localctx.exception = re;
			_errHandler.reportError(this, re);
			_errHandler.recover(this, re);
		}
		finally {
			exitRule();
		}
		return _localctx;
	}

	public static class Start_ListParamDeclContext extends ParserRuleContext {
		public stella.Absyn.ListParamDecl result;
		public ListParamDeclContext x;
		public TerminalNode EOF() { return getToken(stellaParser.EOF, 0); }
		public ListParamDeclContext listParamDecl() {
			return getRuleContext(ListParamDeclContext.class,0);
		}
		public Start_ListParamDeclContext(ParserRuleContext parent, int invokingState) {
			super(parent, invokingState);
		}
		@Override public int getRuleIndex() { return RULE_start_ListParamDecl; }
		@Override
		public void enterRule(ParseTreeListener listener) {
			if ( listener instanceof stellaParserListener ) ((stellaParserListener)listener).enterStart_ListParamDecl(this);
		}
		@Override
		public void exitRule(ParseTreeListener listener) {
			if ( listener instanceof stellaParserListener ) ((stellaParserListener)listener).exitStart_ListParamDecl(this);
		}
	}

	public final Start_ListParamDeclContext start_ListParamDecl() throws RecognitionException {
		Start_ListParamDeclContext _localctx = new Start_ListParamDeclContext(_ctx, getState());
		enterRule(_localctx, 24, RULE_start_ListParamDecl);
		try {
			enterOuterAlt(_localctx, 1);
			{
			setState(200);
			((Start_ListParamDeclContext)_localctx).x = listParamDecl();
			setState(201);
			match(EOF);
			 ((Start_ListParamDeclContext)_localctx).result =  ((Start_ListParamDeclContext)_localctx).x.result; 
			}
		}
		catch (RecognitionException re) {
			_localctx.exception = re;
			_errHandler.reportError(this, re);
			_errHandler.recover(this, re);
		}
		finally {
			exitRule();
		}
		return _localctx;
	}

	public static class Start_ReturnTypeContext extends ParserRuleContext {
		public stella.Absyn.ReturnType result;
		public ReturnTypeContext x;
		public TerminalNode EOF() { return getToken(stellaParser.EOF, 0); }
		public ReturnTypeContext returnType() {
			return getRuleContext(ReturnTypeContext.class,0);
		}
		public Start_ReturnTypeContext(ParserRuleContext parent, int invokingState) {
			super(parent, invokingState);
		}
		@Override public int getRuleIndex() { return RULE_start_ReturnType; }
		@Override
		public void enterRule(ParseTreeListener listener) {
			if ( listener instanceof stellaParserListener ) ((stellaParserListener)listener).enterStart_ReturnType(this);
		}
		@Override
		public void exitRule(ParseTreeListener listener) {
			if ( listener instanceof stellaParserListener ) ((stellaParserListener)listener).exitStart_ReturnType(this);
		}
	}

	public final Start_ReturnTypeContext start_ReturnType() throws RecognitionException {
		Start_ReturnTypeContext _localctx = new Start_ReturnTypeContext(_ctx, getState());
		enterRule(_localctx, 26, RULE_start_ReturnType);
		try {
			enterOuterAlt(_localctx, 1);
			{
			setState(204);
			((Start_ReturnTypeContext)_localctx).x = returnType();
			setState(205);
			match(EOF);
			 ((Start_ReturnTypeContext)_localctx).result =  ((Start_ReturnTypeContext)_localctx).x.result; 
			}
		}
		catch (RecognitionException re) {
			_localctx.exception = re;
			_errHandler.reportError(this, re);
			_errHandler.recover(this, re);
		}
		finally {
			exitRule();
		}
		return _localctx;
	}

	public static class Start_ThrowTypeContext extends ParserRuleContext {
		public stella.Absyn.ThrowType result;
		public ThrowTypeContext x;
		public TerminalNode EOF() { return getToken(stellaParser.EOF, 0); }
		public ThrowTypeContext throwType() {
			return getRuleContext(ThrowTypeContext.class,0);
		}
		public Start_ThrowTypeContext(ParserRuleContext parent, int invokingState) {
			super(parent, invokingState);
		}
		@Override public int getRuleIndex() { return RULE_start_ThrowType; }
		@Override
		public void enterRule(ParseTreeListener listener) {
			if ( listener instanceof stellaParserListener ) ((stellaParserListener)listener).enterStart_ThrowType(this);
		}
		@Override
		public void exitRule(ParseTreeListener listener) {
			if ( listener instanceof stellaParserListener ) ((stellaParserListener)listener).exitStart_ThrowType(this);
		}
	}

	public final Start_ThrowTypeContext start_ThrowType() throws RecognitionException {
		Start_ThrowTypeContext _localctx = new Start_ThrowTypeContext(_ctx, getState());
		enterRule(_localctx, 28, RULE_start_ThrowType);
		try {
			enterOuterAlt(_localctx, 1);
			{
			setState(208);
			((Start_ThrowTypeContext)_localctx).x = throwType();
			setState(209);
			match(EOF);
			 ((Start_ThrowTypeContext)_localctx).result =  ((Start_ThrowTypeContext)_localctx).x.result; 
			}
		}
		catch (RecognitionException re) {
			_localctx.exception = re;
			_errHandler.reportError(this, re);
			_errHandler.recover(this, re);
		}
		finally {
			exitRule();
		}
		return _localctx;
	}

	public static class Start_ExprContext extends ParserRuleContext {
		public stella.Absyn.Expr result;
		public ExprContext x;
		public TerminalNode EOF() { return getToken(stellaParser.EOF, 0); }
		public ExprContext expr() {
			return getRuleContext(ExprContext.class,0);
		}
		public Start_ExprContext(ParserRuleContext parent, int invokingState) {
			super(parent, invokingState);
		}
		@Override public int getRuleIndex() { return RULE_start_Expr; }
		@Override
		public void enterRule(ParseTreeListener listener) {
			if ( listener instanceof stellaParserListener ) ((stellaParserListener)listener).enterStart_Expr(this);
		}
		@Override
		public void exitRule(ParseTreeListener listener) {
			if ( listener instanceof stellaParserListener ) ((stellaParserListener)listener).exitStart_Expr(this);
		}
	}

	public final Start_ExprContext start_Expr() throws RecognitionException {
		Start_ExprContext _localctx = new Start_ExprContext(_ctx, getState());
		enterRule(_localctx, 30, RULE_start_Expr);
		try {
			enterOuterAlt(_localctx, 1);
			{
			setState(212);
			((Start_ExprContext)_localctx).x = expr();
			setState(213);
			match(EOF);
			 ((Start_ExprContext)_localctx).result =  ((Start_ExprContext)_localctx).x.result; 
			}
		}
		catch (RecognitionException re) {
			_localctx.exception = re;
			_errHandler.reportError(this, re);
			_errHandler.recover(this, re);
		}
		finally {
			exitRule();
		}
		return _localctx;
	}

	public static class Start_ListExprContext extends ParserRuleContext {
		public stella.Absyn.ListExpr result;
		public ListExprContext x;
		public TerminalNode EOF() { return getToken(stellaParser.EOF, 0); }
		public ListExprContext listExpr() {
			return getRuleContext(ListExprContext.class,0);
		}
		public Start_ListExprContext(ParserRuleContext parent, int invokingState) {
			super(parent, invokingState);
		}
		@Override public int getRuleIndex() { return RULE_start_ListExpr; }
		@Override
		public void enterRule(ParseTreeListener listener) {
			if ( listener instanceof stellaParserListener ) ((stellaParserListener)listener).enterStart_ListExpr(this);
		}
		@Override
		public void exitRule(ParseTreeListener listener) {
			if ( listener instanceof stellaParserListener ) ((stellaParserListener)listener).exitStart_ListExpr(this);
		}
	}

	public final Start_ListExprContext start_ListExpr() throws RecognitionException {
		Start_ListExprContext _localctx = new Start_ListExprContext(_ctx, getState());
		enterRule(_localctx, 32, RULE_start_ListExpr);
		try {
			enterOuterAlt(_localctx, 1);
			{
			setState(216);
			((Start_ListExprContext)_localctx).x = listExpr();
			setState(217);
			match(EOF);
			 ((Start_ListExprContext)_localctx).result =  ((Start_ListExprContext)_localctx).x.result; 
			}
		}
		catch (RecognitionException re) {
			_localctx.exception = re;
			_errHandler.reportError(this, re);
			_errHandler.recover(this, re);
		}
		finally {
			exitRule();
		}
		return _localctx;
	}

	public static class Start_MatchCaseContext extends ParserRuleContext {
		public stella.Absyn.MatchCase result;
		public MatchCaseContext x;
		public TerminalNode EOF() { return getToken(stellaParser.EOF, 0); }
		public MatchCaseContext matchCase() {
			return getRuleContext(MatchCaseContext.class,0);
		}
		public Start_MatchCaseContext(ParserRuleContext parent, int invokingState) {
			super(parent, invokingState);
		}
		@Override public int getRuleIndex() { return RULE_start_MatchCase; }
		@Override
		public void enterRule(ParseTreeListener listener) {
			if ( listener instanceof stellaParserListener ) ((stellaParserListener)listener).enterStart_MatchCase(this);
		}
		@Override
		public void exitRule(ParseTreeListener listener) {
			if ( listener instanceof stellaParserListener ) ((stellaParserListener)listener).exitStart_MatchCase(this);
		}
	}

	public final Start_MatchCaseContext start_MatchCase() throws RecognitionException {
		Start_MatchCaseContext _localctx = new Start_MatchCaseContext(_ctx, getState());
		enterRule(_localctx, 34, RULE_start_MatchCase);
		try {
			enterOuterAlt(_localctx, 1);
			{
			setState(220);
			((Start_MatchCaseContext)_localctx).x = matchCase();
			setState(221);
			match(EOF);
			 ((Start_MatchCaseContext)_localctx).result =  ((Start_MatchCaseContext)_localctx).x.result; 
			}
		}
		catch (RecognitionException re) {
			_localctx.exception = re;
			_errHandler.reportError(this, re);
			_errHandler.recover(this, re);
		}
		finally {
			exitRule();
		}
		return _localctx;
	}

	public static class Start_ListMatchCaseContext extends ParserRuleContext {
		public stella.Absyn.ListMatchCase result;
		public ListMatchCaseContext x;
		public TerminalNode EOF() { return getToken(stellaParser.EOF, 0); }
		public ListMatchCaseContext listMatchCase() {
			return getRuleContext(ListMatchCaseContext.class,0);
		}
		public Start_ListMatchCaseContext(ParserRuleContext parent, int invokingState) {
			super(parent, invokingState);
		}
		@Override public int getRuleIndex() { return RULE_start_ListMatchCase; }
		@Override
		public void enterRule(ParseTreeListener listener) {
			if ( listener instanceof stellaParserListener ) ((stellaParserListener)listener).enterStart_ListMatchCase(this);
		}
		@Override
		public void exitRule(ParseTreeListener listener) {
			if ( listener instanceof stellaParserListener ) ((stellaParserListener)listener).exitStart_ListMatchCase(this);
		}
	}

	public final Start_ListMatchCaseContext start_ListMatchCase() throws RecognitionException {
		Start_ListMatchCaseContext _localctx = new Start_ListMatchCaseContext(_ctx, getState());
		enterRule(_localctx, 36, RULE_start_ListMatchCase);
		try {
			enterOuterAlt(_localctx, 1);
			{
			setState(224);
			((Start_ListMatchCaseContext)_localctx).x = listMatchCase();
			setState(225);
			match(EOF);
			 ((Start_ListMatchCaseContext)_localctx).result =  ((Start_ListMatchCaseContext)_localctx).x.result; 
			}
		}
		catch (RecognitionException re) {
			_localctx.exception = re;
			_errHandler.reportError(this, re);
			_errHandler.recover(this, re);
		}
		finally {
			exitRule();
		}
		return _localctx;
	}

	public static class Start_PatternContext extends ParserRuleContext {
		public stella.Absyn.Pattern result;
		public PatternContext x;
		public TerminalNode EOF() { return getToken(stellaParser.EOF, 0); }
		public PatternContext pattern() {
			return getRuleContext(PatternContext.class,0);
		}
		public Start_PatternContext(ParserRuleContext parent, int invokingState) {
			super(parent, invokingState);
		}
		@Override public int getRuleIndex() { return RULE_start_Pattern; }
		@Override
		public void enterRule(ParseTreeListener listener) {
			if ( listener instanceof stellaParserListener ) ((stellaParserListener)listener).enterStart_Pattern(this);
		}
		@Override
		public void exitRule(ParseTreeListener listener) {
			if ( listener instanceof stellaParserListener ) ((stellaParserListener)listener).exitStart_Pattern(this);
		}
	}

	public final Start_PatternContext start_Pattern() throws RecognitionException {
		Start_PatternContext _localctx = new Start_PatternContext(_ctx, getState());
		enterRule(_localctx, 38, RULE_start_Pattern);
		try {
			enterOuterAlt(_localctx, 1);
			{
			setState(228);
			((Start_PatternContext)_localctx).x = pattern();
			setState(229);
			match(EOF);
			 ((Start_PatternContext)_localctx).result =  ((Start_PatternContext)_localctx).x.result; 
			}
		}
		catch (RecognitionException re) {
			_localctx.exception = re;
			_errHandler.reportError(this, re);
			_errHandler.recover(this, re);
		}
		finally {
			exitRule();
		}
		return _localctx;
	}

	public static class Start_ListPatternContext extends ParserRuleContext {
		public stella.Absyn.ListPattern result;
		public ListPatternContext x;
		public TerminalNode EOF() { return getToken(stellaParser.EOF, 0); }
		public ListPatternContext listPattern() {
			return getRuleContext(ListPatternContext.class,0);
		}
		public Start_ListPatternContext(ParserRuleContext parent, int invokingState) {
			super(parent, invokingState);
		}
		@Override public int getRuleIndex() { return RULE_start_ListPattern; }
		@Override
		public void enterRule(ParseTreeListener listener) {
			if ( listener instanceof stellaParserListener ) ((stellaParserListener)listener).enterStart_ListPattern(this);
		}
		@Override
		public void exitRule(ParseTreeListener listener) {
			if ( listener instanceof stellaParserListener ) ((stellaParserListener)listener).exitStart_ListPattern(this);
		}
	}

	public final Start_ListPatternContext start_ListPattern() throws RecognitionException {
		Start_ListPatternContext _localctx = new Start_ListPatternContext(_ctx, getState());
		enterRule(_localctx, 40, RULE_start_ListPattern);
		try {
			enterOuterAlt(_localctx, 1);
			{
			setState(232);
			((Start_ListPatternContext)_localctx).x = listPattern();
			setState(233);
			match(EOF);
			 ((Start_ListPatternContext)_localctx).result =  ((Start_ListPatternContext)_localctx).x.result; 
			}
		}
		catch (RecognitionException re) {
			_localctx.exception = re;
			_errHandler.reportError(this, re);
			_errHandler.recover(this, re);
		}
		finally {
			exitRule();
		}
		return _localctx;
	}

	public static class Start_LabelledPatternContext extends ParserRuleContext {
		public stella.Absyn.LabelledPattern result;
		public LabelledPatternContext x;
		public TerminalNode EOF() { return getToken(stellaParser.EOF, 0); }
		public LabelledPatternContext labelledPattern() {
			return getRuleContext(LabelledPatternContext.class,0);
		}
		public Start_LabelledPatternContext(ParserRuleContext parent, int invokingState) {
			super(parent, invokingState);
		}
		@Override public int getRuleIndex() { return RULE_start_LabelledPattern; }
		@Override
		public void enterRule(ParseTreeListener listener) {
			if ( listener instanceof stellaParserListener ) ((stellaParserListener)listener).enterStart_LabelledPattern(this);
		}
		@Override
		public void exitRule(ParseTreeListener listener) {
			if ( listener instanceof stellaParserListener ) ((stellaParserListener)listener).exitStart_LabelledPattern(this);
		}
	}

	public final Start_LabelledPatternContext start_LabelledPattern() throws RecognitionException {
		Start_LabelledPatternContext _localctx = new Start_LabelledPatternContext(_ctx, getState());
		enterRule(_localctx, 42, RULE_start_LabelledPattern);
		try {
			enterOuterAlt(_localctx, 1);
			{
			setState(236);
			((Start_LabelledPatternContext)_localctx).x = labelledPattern();
			setState(237);
			match(EOF);
			 ((Start_LabelledPatternContext)_localctx).result =  ((Start_LabelledPatternContext)_localctx).x.result; 
			}
		}
		catch (RecognitionException re) {
			_localctx.exception = re;
			_errHandler.reportError(this, re);
			_errHandler.recover(this, re);
		}
		finally {
			exitRule();
		}
		return _localctx;
	}

	public static class Start_ListLabelledPatternContext extends ParserRuleContext {
		public stella.Absyn.ListLabelledPattern result;
		public ListLabelledPatternContext x;
		public TerminalNode EOF() { return getToken(stellaParser.EOF, 0); }
		public ListLabelledPatternContext listLabelledPattern() {
			return getRuleContext(ListLabelledPatternContext.class,0);
		}
		public Start_ListLabelledPatternContext(ParserRuleContext parent, int invokingState) {
			super(parent, invokingState);
		}
		@Override public int getRuleIndex() { return RULE_start_ListLabelledPattern; }
		@Override
		public void enterRule(ParseTreeListener listener) {
			if ( listener instanceof stellaParserListener ) ((stellaParserListener)listener).enterStart_ListLabelledPattern(this);
		}
		@Override
		public void exitRule(ParseTreeListener listener) {
			if ( listener instanceof stellaParserListener ) ((stellaParserListener)listener).exitStart_ListLabelledPattern(this);
		}
	}

	public final Start_ListLabelledPatternContext start_ListLabelledPattern() throws RecognitionException {
		Start_ListLabelledPatternContext _localctx = new Start_ListLabelledPatternContext(_ctx, getState());
		enterRule(_localctx, 44, RULE_start_ListLabelledPattern);
		try {
			enterOuterAlt(_localctx, 1);
			{
			setState(240);
			((Start_ListLabelledPatternContext)_localctx).x = listLabelledPattern();
			setState(241);
			match(EOF);
			 ((Start_ListLabelledPatternContext)_localctx).result =  ((Start_ListLabelledPatternContext)_localctx).x.result; 
			}
		}
		catch (RecognitionException re) {
			_localctx.exception = re;
			_errHandler.reportError(this, re);
			_errHandler.recover(this, re);
		}
		finally {
			exitRule();
		}
		return _localctx;
	}

	public static class Start_BindingContext extends ParserRuleContext {
		public stella.Absyn.Binding result;
		public BindingContext x;
		public TerminalNode EOF() { return getToken(stellaParser.EOF, 0); }
		public BindingContext binding() {
			return getRuleContext(BindingContext.class,0);
		}
		public Start_BindingContext(ParserRuleContext parent, int invokingState) {
			super(parent, invokingState);
		}
		@Override public int getRuleIndex() { return RULE_start_Binding; }
		@Override
		public void enterRule(ParseTreeListener listener) {
			if ( listener instanceof stellaParserListener ) ((stellaParserListener)listener).enterStart_Binding(this);
		}
		@Override
		public void exitRule(ParseTreeListener listener) {
			if ( listener instanceof stellaParserListener ) ((stellaParserListener)listener).exitStart_Binding(this);
		}
	}

	public final Start_BindingContext start_Binding() throws RecognitionException {
		Start_BindingContext _localctx = new Start_BindingContext(_ctx, getState());
		enterRule(_localctx, 46, RULE_start_Binding);
		try {
			enterOuterAlt(_localctx, 1);
			{
			setState(244);
			((Start_BindingContext)_localctx).x = binding();
			setState(245);
			match(EOF);
			 ((Start_BindingContext)_localctx).result =  ((Start_BindingContext)_localctx).x.result; 
			}
		}
		catch (RecognitionException re) {
			_localctx.exception = re;
			_errHandler.reportError(this, re);
			_errHandler.recover(this, re);
		}
		finally {
			exitRule();
		}
		return _localctx;
	}

	public static class Start_ListBindingContext extends ParserRuleContext {
		public stella.Absyn.ListBinding result;
		public ListBindingContext x;
		public TerminalNode EOF() { return getToken(stellaParser.EOF, 0); }
		public ListBindingContext listBinding() {
			return getRuleContext(ListBindingContext.class,0);
		}
		public Start_ListBindingContext(ParserRuleContext parent, int invokingState) {
			super(parent, invokingState);
		}
		@Override public int getRuleIndex() { return RULE_start_ListBinding; }
		@Override
		public void enterRule(ParseTreeListener listener) {
			if ( listener instanceof stellaParserListener ) ((stellaParserListener)listener).enterStart_ListBinding(this);
		}
		@Override
		public void exitRule(ParseTreeListener listener) {
			if ( listener instanceof stellaParserListener ) ((stellaParserListener)listener).exitStart_ListBinding(this);
		}
	}

	public final Start_ListBindingContext start_ListBinding() throws RecognitionException {
		Start_ListBindingContext _localctx = new Start_ListBindingContext(_ctx, getState());
		enterRule(_localctx, 48, RULE_start_ListBinding);
		try {
			enterOuterAlt(_localctx, 1);
			{
			setState(248);
			((Start_ListBindingContext)_localctx).x = listBinding();
			setState(249);
			match(EOF);
			 ((Start_ListBindingContext)_localctx).result =  ((Start_ListBindingContext)_localctx).x.result; 
			}
		}
		catch (RecognitionException re) {
			_localctx.exception = re;
			_errHandler.reportError(this, re);
			_errHandler.recover(this, re);
		}
		finally {
			exitRule();
		}
		return _localctx;
	}

	public static class Start_Expr0Context extends ParserRuleContext {
		public stella.Absyn.Expr result;
		public Expr0Context x;
		public TerminalNode EOF() { return getToken(stellaParser.EOF, 0); }
		public Expr0Context expr0() {
			return getRuleContext(Expr0Context.class,0);
		}
		public Start_Expr0Context(ParserRuleContext parent, int invokingState) {
			super(parent, invokingState);
		}
		@Override public int getRuleIndex() { return RULE_start_Expr0; }
		@Override
		public void enterRule(ParseTreeListener listener) {
			if ( listener instanceof stellaParserListener ) ((stellaParserListener)listener).enterStart_Expr0(this);
		}
		@Override
		public void exitRule(ParseTreeListener listener) {
			if ( listener instanceof stellaParserListener ) ((stellaParserListener)listener).exitStart_Expr0(this);
		}
	}

	public final Start_Expr0Context start_Expr0() throws RecognitionException {
		Start_Expr0Context _localctx = new Start_Expr0Context(_ctx, getState());
		enterRule(_localctx, 50, RULE_start_Expr0);
		try {
			enterOuterAlt(_localctx, 1);
			{
			setState(252);
			((Start_Expr0Context)_localctx).x = expr0();
			setState(253);
			match(EOF);
			 ((Start_Expr0Context)_localctx).result =  ((Start_Expr0Context)_localctx).x.result; 
			}
		}
		catch (RecognitionException re) {
			_localctx.exception = re;
			_errHandler.reportError(this, re);
			_errHandler.recover(this, re);
		}
		finally {
			exitRule();
		}
		return _localctx;
	}

	public static class Start_Expr1Context extends ParserRuleContext {
		public stella.Absyn.Expr result;
		public Expr1Context x;
		public TerminalNode EOF() { return getToken(stellaParser.EOF, 0); }
		public Expr1Context expr1() {
			return getRuleContext(Expr1Context.class,0);
		}
		public Start_Expr1Context(ParserRuleContext parent, int invokingState) {
			super(parent, invokingState);
		}
		@Override public int getRuleIndex() { return RULE_start_Expr1; }
		@Override
		public void enterRule(ParseTreeListener listener) {
			if ( listener instanceof stellaParserListener ) ((stellaParserListener)listener).enterStart_Expr1(this);
		}
		@Override
		public void exitRule(ParseTreeListener listener) {
			if ( listener instanceof stellaParserListener ) ((stellaParserListener)listener).exitStart_Expr1(this);
		}
	}

	public final Start_Expr1Context start_Expr1() throws RecognitionException {
		Start_Expr1Context _localctx = new Start_Expr1Context(_ctx, getState());
		enterRule(_localctx, 52, RULE_start_Expr1);
		try {
			enterOuterAlt(_localctx, 1);
			{
			setState(256);
			((Start_Expr1Context)_localctx).x = expr1(0);
			setState(257);
			match(EOF);
			 ((Start_Expr1Context)_localctx).result =  ((Start_Expr1Context)_localctx).x.result; 
			}
		}
		catch (RecognitionException re) {
			_localctx.exception = re;
			_errHandler.reportError(this, re);
			_errHandler.recover(this, re);
		}
		finally {
			exitRule();
		}
		return _localctx;
	}

	public static class Start_Expr2Context extends ParserRuleContext {
		public stella.Absyn.Expr result;
		public Expr2Context x;
		public TerminalNode EOF() { return getToken(stellaParser.EOF, 0); }
		public Expr2Context expr2() {
			return getRuleContext(Expr2Context.class,0);
		}
		public Start_Expr2Context(ParserRuleContext parent, int invokingState) {
			super(parent, invokingState);
		}
		@Override public int getRuleIndex() { return RULE_start_Expr2; }
		@Override
		public void enterRule(ParseTreeListener listener) {
			if ( listener instanceof stellaParserListener ) ((stellaParserListener)listener).enterStart_Expr2(this);
		}
		@Override
		public void exitRule(ParseTreeListener listener) {
			if ( listener instanceof stellaParserListener ) ((stellaParserListener)listener).exitStart_Expr2(this);
		}
	}

	public final Start_Expr2Context start_Expr2() throws RecognitionException {
		Start_Expr2Context _localctx = new Start_Expr2Context(_ctx, getState());
		enterRule(_localctx, 54, RULE_start_Expr2);
		try {
			enterOuterAlt(_localctx, 1);
			{
			setState(260);
			((Start_Expr2Context)_localctx).x = expr2(0);
			setState(261);
			match(EOF);
			 ((Start_Expr2Context)_localctx).result =  ((Start_Expr2Context)_localctx).x.result; 
			}
		}
		catch (RecognitionException re) {
			_localctx.exception = re;
			_errHandler.reportError(this, re);
			_errHandler.recover(this, re);
		}
		finally {
			exitRule();
		}
		return _localctx;
	}

	public static class Start_Expr3Context extends ParserRuleContext {
		public stella.Absyn.Expr result;
		public Expr3Context x;
		public TerminalNode EOF() { return getToken(stellaParser.EOF, 0); }
		public Expr3Context expr3() {
			return getRuleContext(Expr3Context.class,0);
		}
		public Start_Expr3Context(ParserRuleContext parent, int invokingState) {
			super(parent, invokingState);
		}
		@Override public int getRuleIndex() { return RULE_start_Expr3; }
		@Override
		public void enterRule(ParseTreeListener listener) {
			if ( listener instanceof stellaParserListener ) ((stellaParserListener)listener).enterStart_Expr3(this);
		}
		@Override
		public void exitRule(ParseTreeListener listener) {
			if ( listener instanceof stellaParserListener ) ((stellaParserListener)listener).exitStart_Expr3(this);
		}
	}

	public final Start_Expr3Context start_Expr3() throws RecognitionException {
		Start_Expr3Context _localctx = new Start_Expr3Context(_ctx, getState());
		enterRule(_localctx, 56, RULE_start_Expr3);
		try {
			enterOuterAlt(_localctx, 1);
			{
			setState(264);
			((Start_Expr3Context)_localctx).x = expr3(0);
			setState(265);
			match(EOF);
			 ((Start_Expr3Context)_localctx).result =  ((Start_Expr3Context)_localctx).x.result; 
			}
		}
		catch (RecognitionException re) {
			_localctx.exception = re;
			_errHandler.reportError(this, re);
			_errHandler.recover(this, re);
		}
		finally {
			exitRule();
		}
		return _localctx;
	}

	public static class Start_Expr4Context extends ParserRuleContext {
		public stella.Absyn.Expr result;
		public Expr4Context x;
		public TerminalNode EOF() { return getToken(stellaParser.EOF, 0); }
		public Expr4Context expr4() {
			return getRuleContext(Expr4Context.class,0);
		}
		public Start_Expr4Context(ParserRuleContext parent, int invokingState) {
			super(parent, invokingState);
		}
		@Override public int getRuleIndex() { return RULE_start_Expr4; }
		@Override
		public void enterRule(ParseTreeListener listener) {
			if ( listener instanceof stellaParserListener ) ((stellaParserListener)listener).enterStart_Expr4(this);
		}
		@Override
		public void exitRule(ParseTreeListener listener) {
			if ( listener instanceof stellaParserListener ) ((stellaParserListener)listener).exitStart_Expr4(this);
		}
	}

	public final Start_Expr4Context start_Expr4() throws RecognitionException {
		Start_Expr4Context _localctx = new Start_Expr4Context(_ctx, getState());
		enterRule(_localctx, 58, RULE_start_Expr4);
		try {
			enterOuterAlt(_localctx, 1);
			{
			setState(268);
			((Start_Expr4Context)_localctx).x = expr4();
			setState(269);
			match(EOF);
			 ((Start_Expr4Context)_localctx).result =  ((Start_Expr4Context)_localctx).x.result; 
			}
		}
		catch (RecognitionException re) {
			_localctx.exception = re;
			_errHandler.reportError(this, re);
			_errHandler.recover(this, re);
		}
		finally {
			exitRule();
		}
		return _localctx;
	}

	public static class Start_Expr5Context extends ParserRuleContext {
		public stella.Absyn.Expr result;
		public Expr5Context x;
		public TerminalNode EOF() { return getToken(stellaParser.EOF, 0); }
		public Expr5Context expr5() {
			return getRuleContext(Expr5Context.class,0);
		}
		public Start_Expr5Context(ParserRuleContext parent, int invokingState) {
			super(parent, invokingState);
		}
		@Override public int getRuleIndex() { return RULE_start_Expr5; }
		@Override
		public void enterRule(ParseTreeListener listener) {
			if ( listener instanceof stellaParserListener ) ((stellaParserListener)listener).enterStart_Expr5(this);
		}
		@Override
		public void exitRule(ParseTreeListener listener) {
			if ( listener instanceof stellaParserListener ) ((stellaParserListener)listener).exitStart_Expr5(this);
		}
	}

	public final Start_Expr5Context start_Expr5() throws RecognitionException {
		Start_Expr5Context _localctx = new Start_Expr5Context(_ctx, getState());
		enterRule(_localctx, 60, RULE_start_Expr5);
		try {
			enterOuterAlt(_localctx, 1);
			{
			setState(272);
			((Start_Expr5Context)_localctx).x = expr5(0);
			setState(273);
			match(EOF);
			 ((Start_Expr5Context)_localctx).result =  ((Start_Expr5Context)_localctx).x.result; 
			}
		}
		catch (RecognitionException re) {
			_localctx.exception = re;
			_errHandler.reportError(this, re);
			_errHandler.recover(this, re);
		}
		finally {
			exitRule();
		}
		return _localctx;
	}

	public static class Start_TypeContext extends ParserRuleContext {
		public stella.Absyn.Type result;
		public TypeContext x;
		public TerminalNode EOF() { return getToken(stellaParser.EOF, 0); }
		public TypeContext type() {
			return getRuleContext(TypeContext.class,0);
		}
		public Start_TypeContext(ParserRuleContext parent, int invokingState) {
			super(parent, invokingState);
		}
		@Override public int getRuleIndex() { return RULE_start_Type; }
		@Override
		public void enterRule(ParseTreeListener listener) {
			if ( listener instanceof stellaParserListener ) ((stellaParserListener)listener).enterStart_Type(this);
		}
		@Override
		public void exitRule(ParseTreeListener listener) {
			if ( listener instanceof stellaParserListener ) ((stellaParserListener)listener).exitStart_Type(this);
		}
	}

	public final Start_TypeContext start_Type() throws RecognitionException {
		Start_TypeContext _localctx = new Start_TypeContext(_ctx, getState());
		enterRule(_localctx, 62, RULE_start_Type);
		try {
			enterOuterAlt(_localctx, 1);
			{
			setState(276);
			((Start_TypeContext)_localctx).x = type();
			setState(277);
			match(EOF);
			 ((Start_TypeContext)_localctx).result =  ((Start_TypeContext)_localctx).x.result; 
			}
		}
		catch (RecognitionException re) {
			_localctx.exception = re;
			_errHandler.reportError(this, re);
			_errHandler.recover(this, re);
		}
		finally {
			exitRule();
		}
		return _localctx;
	}

	public static class Start_Type1Context extends ParserRuleContext {
		public stella.Absyn.Type result;
		public Type1Context x;
		public TerminalNode EOF() { return getToken(stellaParser.EOF, 0); }
		public Type1Context type1() {
			return getRuleContext(Type1Context.class,0);
		}
		public Start_Type1Context(ParserRuleContext parent, int invokingState) {
			super(parent, invokingState);
		}
		@Override public int getRuleIndex() { return RULE_start_Type1; }
		@Override
		public void enterRule(ParseTreeListener listener) {
			if ( listener instanceof stellaParserListener ) ((stellaParserListener)listener).enterStart_Type1(this);
		}
		@Override
		public void exitRule(ParseTreeListener listener) {
			if ( listener instanceof stellaParserListener ) ((stellaParserListener)listener).exitStart_Type1(this);
		}
	}

	public final Start_Type1Context start_Type1() throws RecognitionException {
		Start_Type1Context _localctx = new Start_Type1Context(_ctx, getState());
		enterRule(_localctx, 64, RULE_start_Type1);
		try {
			enterOuterAlt(_localctx, 1);
			{
			setState(280);
			((Start_Type1Context)_localctx).x = type1();
			setState(281);
			match(EOF);
			 ((Start_Type1Context)_localctx).result =  ((Start_Type1Context)_localctx).x.result; 
			}
		}
		catch (RecognitionException re) {
			_localctx.exception = re;
			_errHandler.reportError(this, re);
			_errHandler.recover(this, re);
		}
		finally {
			exitRule();
		}
		return _localctx;
	}

	public static class Start_Type2Context extends ParserRuleContext {
		public stella.Absyn.Type result;
		public Type2Context x;
		public TerminalNode EOF() { return getToken(stellaParser.EOF, 0); }
		public Type2Context type2() {
			return getRuleContext(Type2Context.class,0);
		}
		public Start_Type2Context(ParserRuleContext parent, int invokingState) {
			super(parent, invokingState);
		}
		@Override public int getRuleIndex() { return RULE_start_Type2; }
		@Override
		public void enterRule(ParseTreeListener listener) {
			if ( listener instanceof stellaParserListener ) ((stellaParserListener)listener).enterStart_Type2(this);
		}
		@Override
		public void exitRule(ParseTreeListener listener) {
			if ( listener instanceof stellaParserListener ) ((stellaParserListener)listener).exitStart_Type2(this);
		}
	}

	public final Start_Type2Context start_Type2() throws RecognitionException {
		Start_Type2Context _localctx = new Start_Type2Context(_ctx, getState());
		enterRule(_localctx, 66, RULE_start_Type2);
		try {
			enterOuterAlt(_localctx, 1);
			{
			setState(284);
			((Start_Type2Context)_localctx).x = type2();
			setState(285);
			match(EOF);
			 ((Start_Type2Context)_localctx).result =  ((Start_Type2Context)_localctx).x.result; 
			}
		}
		catch (RecognitionException re) {
			_localctx.exception = re;
			_errHandler.reportError(this, re);
			_errHandler.recover(this, re);
		}
		finally {
			exitRule();
		}
		return _localctx;
	}

	public static class Start_ListTypeContext extends ParserRuleContext {
		public stella.Absyn.ListType result;
		public ListTypeContext x;
		public TerminalNode EOF() { return getToken(stellaParser.EOF, 0); }
		public ListTypeContext listType() {
			return getRuleContext(ListTypeContext.class,0);
		}
		public Start_ListTypeContext(ParserRuleContext parent, int invokingState) {
			super(parent, invokingState);
		}
		@Override public int getRuleIndex() { return RULE_start_ListType; }
		@Override
		public void enterRule(ParseTreeListener listener) {
			if ( listener instanceof stellaParserListener ) ((stellaParserListener)listener).enterStart_ListType(this);
		}
		@Override
		public void exitRule(ParseTreeListener listener) {
			if ( listener instanceof stellaParserListener ) ((stellaParserListener)listener).exitStart_ListType(this);
		}
	}

	public final Start_ListTypeContext start_ListType() throws RecognitionException {
		Start_ListTypeContext _localctx = new Start_ListTypeContext(_ctx, getState());
		enterRule(_localctx, 68, RULE_start_ListType);
		try {
			enterOuterAlt(_localctx, 1);
			{
			setState(288);
			((Start_ListTypeContext)_localctx).x = listType();
			setState(289);
			match(EOF);
			 ((Start_ListTypeContext)_localctx).result =  ((Start_ListTypeContext)_localctx).x.result; 
			}
		}
		catch (RecognitionException re) {
			_localctx.exception = re;
			_errHandler.reportError(this, re);
			_errHandler.recover(this, re);
		}
		finally {
			exitRule();
		}
		return _localctx;
	}

	public static class Start_FieldTypeContext extends ParserRuleContext {
		public stella.Absyn.FieldType result;
		public FieldTypeContext x;
		public TerminalNode EOF() { return getToken(stellaParser.EOF, 0); }
		public FieldTypeContext fieldType() {
			return getRuleContext(FieldTypeContext.class,0);
		}
		public Start_FieldTypeContext(ParserRuleContext parent, int invokingState) {
			super(parent, invokingState);
		}
		@Override public int getRuleIndex() { return RULE_start_FieldType; }
		@Override
		public void enterRule(ParseTreeListener listener) {
			if ( listener instanceof stellaParserListener ) ((stellaParserListener)listener).enterStart_FieldType(this);
		}
		@Override
		public void exitRule(ParseTreeListener listener) {
			if ( listener instanceof stellaParserListener ) ((stellaParserListener)listener).exitStart_FieldType(this);
		}
	}

	public final Start_FieldTypeContext start_FieldType() throws RecognitionException {
		Start_FieldTypeContext _localctx = new Start_FieldTypeContext(_ctx, getState());
		enterRule(_localctx, 70, RULE_start_FieldType);
		try {
			enterOuterAlt(_localctx, 1);
			{
			setState(292);
			((Start_FieldTypeContext)_localctx).x = fieldType();
			setState(293);
			match(EOF);
			 ((Start_FieldTypeContext)_localctx).result =  ((Start_FieldTypeContext)_localctx).x.result; 
			}
		}
		catch (RecognitionException re) {
			_localctx.exception = re;
			_errHandler.reportError(this, re);
			_errHandler.recover(this, re);
		}
		finally {
			exitRule();
		}
		return _localctx;
	}

	public static class Start_ListFieldTypeContext extends ParserRuleContext {
		public stella.Absyn.ListFieldType result;
		public ListFieldTypeContext x;
		public TerminalNode EOF() { return getToken(stellaParser.EOF, 0); }
		public ListFieldTypeContext listFieldType() {
			return getRuleContext(ListFieldTypeContext.class,0);
		}
		public Start_ListFieldTypeContext(ParserRuleContext parent, int invokingState) {
			super(parent, invokingState);
		}
		@Override public int getRuleIndex() { return RULE_start_ListFieldType; }
		@Override
		public void enterRule(ParseTreeListener listener) {
			if ( listener instanceof stellaParserListener ) ((stellaParserListener)listener).enterStart_ListFieldType(this);
		}
		@Override
		public void exitRule(ParseTreeListener listener) {
			if ( listener instanceof stellaParserListener ) ((stellaParserListener)listener).exitStart_ListFieldType(this);
		}
	}

	public final Start_ListFieldTypeContext start_ListFieldType() throws RecognitionException {
		Start_ListFieldTypeContext _localctx = new Start_ListFieldTypeContext(_ctx, getState());
		enterRule(_localctx, 72, RULE_start_ListFieldType);
		try {
			enterOuterAlt(_localctx, 1);
			{
			setState(296);
			((Start_ListFieldTypeContext)_localctx).x = listFieldType();
			setState(297);
			match(EOF);
			 ((Start_ListFieldTypeContext)_localctx).result =  ((Start_ListFieldTypeContext)_localctx).x.result; 
			}
		}
		catch (RecognitionException re) {
			_localctx.exception = re;
			_errHandler.reportError(this, re);
			_errHandler.recover(this, re);
		}
		finally {
			exitRule();
		}
		return _localctx;
	}

	public static class Start_TypingContext extends ParserRuleContext {
		public stella.Absyn.Typing result;
		public TypingContext x;
		public TerminalNode EOF() { return getToken(stellaParser.EOF, 0); }
		public TypingContext typing() {
			return getRuleContext(TypingContext.class,0);
		}
		public Start_TypingContext(ParserRuleContext parent, int invokingState) {
			super(parent, invokingState);
		}
		@Override public int getRuleIndex() { return RULE_start_Typing; }
		@Override
		public void enterRule(ParseTreeListener listener) {
			if ( listener instanceof stellaParserListener ) ((stellaParserListener)listener).enterStart_Typing(this);
		}
		@Override
		public void exitRule(ParseTreeListener listener) {
			if ( listener instanceof stellaParserListener ) ((stellaParserListener)listener).exitStart_Typing(this);
		}
	}

	public final Start_TypingContext start_Typing() throws RecognitionException {
		Start_TypingContext _localctx = new Start_TypingContext(_ctx, getState());
		enterRule(_localctx, 74, RULE_start_Typing);
		try {
			enterOuterAlt(_localctx, 1);
			{
			setState(300);
			((Start_TypingContext)_localctx).x = typing();
			setState(301);
			match(EOF);
			 ((Start_TypingContext)_localctx).result =  ((Start_TypingContext)_localctx).x.result; 
			}
		}
		catch (RecognitionException re) {
			_localctx.exception = re;
			_errHandler.reportError(this, re);
			_errHandler.recover(this, re);
		}
		finally {
			exitRule();
		}
		return _localctx;
	}

	public static class ProgramContext extends ParserRuleContext {
		public stella.Absyn.Program result;
		public LanguageDeclContext p_1_1;
		public ListExtensionContext p_1_2;
		public ListDeclContext p_1_3;
		public LanguageDeclContext languageDecl() {
			return getRuleContext(LanguageDeclContext.class,0);
		}
		public ListExtensionContext listExtension() {
			return getRuleContext(ListExtensionContext.class,0);
		}
		public ListDeclContext listDecl() {
			return getRuleContext(ListDeclContext.class,0);
		}
		public ProgramContext(ParserRuleContext parent, int invokingState) {
			super(parent, invokingState);
		}
		@Override public int getRuleIndex() { return RULE_program; }
		@Override
		public void enterRule(ParseTreeListener listener) {
			if ( listener instanceof stellaParserListener ) ((stellaParserListener)listener).enterProgram(this);
		}
		@Override
		public void exitRule(ParseTreeListener listener) {
			if ( listener instanceof stellaParserListener ) ((stellaParserListener)listener).exitProgram(this);
		}
	}

	public final ProgramContext program() throws RecognitionException {
		ProgramContext _localctx = new ProgramContext(_ctx, getState());
		enterRule(_localctx, 76, RULE_program);
		try {
			enterOuterAlt(_localctx, 1);
			{
			setState(304);
			((ProgramContext)_localctx).p_1_1 = languageDecl();
			setState(305);
			((ProgramContext)_localctx).p_1_2 = listExtension(0);
			setState(306);
			((ProgramContext)_localctx).p_1_3 = listDecl(0);
			 ((ProgramContext)_localctx).result =  new stella.Absyn.AProgram(((ProgramContext)_localctx).p_1_1.result,((ProgramContext)_localctx).p_1_2.result,((ProgramContext)_localctx).p_1_3.result); 
			}
		}
		catch (RecognitionException re) {
			_localctx.exception = re;
			_errHandler.reportError(this, re);
			_errHandler.recover(this, re);
		}
		finally {
			exitRule();
		}
		return _localctx;
	}

	public static class LanguageDeclContext extends ParserRuleContext {
		public stella.Absyn.LanguageDecl result;
		public TerminalNode Surrogate_id_SYMB_43() { return getToken(stellaParser.Surrogate_id_SYMB_43, 0); }
		public TerminalNode Surrogate_id_SYMB_33() { return getToken(stellaParser.Surrogate_id_SYMB_33, 0); }
		public TerminalNode Surrogate_id_SYMB_0() { return getToken(stellaParser.Surrogate_id_SYMB_0, 0); }
		public LanguageDeclContext(ParserRuleContext parent, int invokingState) {
			super(parent, invokingState);
		}
		@Override public int getRuleIndex() { return RULE_languageDecl; }
		@Override
		public void enterRule(ParseTreeListener listener) {
			if ( listener instanceof stellaParserListener ) ((stellaParserListener)listener).enterLanguageDecl(this);
		}
		@Override
		public void exitRule(ParseTreeListener listener) {
			if ( listener instanceof stellaParserListener ) ((stellaParserListener)listener).exitLanguageDecl(this);
		}
	}

	public final LanguageDeclContext languageDecl() throws RecognitionException {
		LanguageDeclContext _localctx = new LanguageDeclContext(_ctx, getState());
		enterRule(_localctx, 78, RULE_languageDecl);
		try {
			enterOuterAlt(_localctx, 1);
			{
			setState(309);
			match(Surrogate_id_SYMB_43);
			setState(310);
			match(Surrogate_id_SYMB_33);
			setState(311);
			match(Surrogate_id_SYMB_0);
			 ((LanguageDeclContext)_localctx).result =  new stella.Absyn.LanguageCore(); 
			}
		}
		catch (RecognitionException re) {
			_localctx.exception = re;
			_errHandler.reportError(this, re);
			_errHandler.recover(this, re);
		}
		finally {
			exitRule();
		}
		return _localctx;
	}

	public static class ExtensionContext extends ParserRuleContext {
		public stella.Absyn.Extension result;
		public ListExtensionNameContext p_1_3;
		public TerminalNode Surrogate_id_SYMB_35() { return getToken(stellaParser.Surrogate_id_SYMB_35, 0); }
		public TerminalNode Surrogate_id_SYMB_58() { return getToken(stellaParser.Surrogate_id_SYMB_58, 0); }
		public ListExtensionNameContext listExtensionName() {
			return getRuleContext(ListExtensionNameContext.class,0);
		}
		public ExtensionContext(ParserRuleContext parent, int invokingState) {
			super(parent, invokingState);
		}
		@Override public int getRuleIndex() { return RULE_extension; }
		@Override
		public void enterRule(ParseTreeListener listener) {
			if ( listener instanceof stellaParserListener ) ((stellaParserListener)listener).enterExtension(this);
		}
		@Override
		public void exitRule(ParseTreeListener listener) {
			if ( listener instanceof stellaParserListener ) ((stellaParserListener)listener).exitExtension(this);
		}
	}

	public final ExtensionContext extension() throws RecognitionException {
		ExtensionContext _localctx = new ExtensionContext(_ctx, getState());
		enterRule(_localctx, 80, RULE_extension);
		try {
			enterOuterAlt(_localctx, 1);
			{
			setState(314);
			match(Surrogate_id_SYMB_35);
			setState(315);
			match(Surrogate_id_SYMB_58);
			setState(316);
			((ExtensionContext)_localctx).p_1_3 = listExtensionName();
			 ((ExtensionContext)_localctx).result =  new stella.Absyn.AnExtension(((ExtensionContext)_localctx).p_1_3.result); 
			}
		}
		catch (RecognitionException re) {
			_localctx.exception = re;
			_errHandler.reportError(this, re);
			_errHandler.recover(this, re);
		}
		finally {
			exitRule();
		}
		return _localctx;
	}

	public static class ListExtensionNameContext extends ParserRuleContext {
		public stella.Absyn.ListExtensionName result;
		public Token p_2_1;
		public Token p_3_1;
		public ListExtensionNameContext p_3_3;
		public TerminalNode ExtensionName() { return getToken(stellaParser.ExtensionName, 0); }
		public TerminalNode Surrogate_id_SYMB_1() { return getToken(stellaParser.Surrogate_id_SYMB_1, 0); }
		public ListExtensionNameContext listExtensionName() {
			return getRuleContext(ListExtensionNameContext.class,0);
		}
		public ListExtensionNameContext(ParserRuleContext parent, int invokingState) {
			super(parent, invokingState);
		}
		@Override public int getRuleIndex() { return RULE_listExtensionName; }
		@Override
		public void enterRule(ParseTreeListener listener) {
			if ( listener instanceof stellaParserListener ) ((stellaParserListener)listener).enterListExtensionName(this);
		}
		@Override
		public void exitRule(ParseTreeListener listener) {
			if ( listener instanceof stellaParserListener ) ((stellaParserListener)listener).exitListExtensionName(this);
		}
	}

	public final ListExtensionNameContext listExtensionName() throws RecognitionException {
		ListExtensionNameContext _localctx = new ListExtensionNameContext(_ctx, getState());
		enterRule(_localctx, 82, RULE_listExtensionName);
		try {
			setState(327);
			_errHandler.sync(this);
			switch ( getInterpreter().adaptivePredict(_input,0,_ctx) ) {
			case 1:
				enterOuterAlt(_localctx, 1);
				{
				 ((ListExtensionNameContext)_localctx).result =  new stella.Absyn.ListExtensionName(); 
				}
				break;
			case 2:
				enterOuterAlt(_localctx, 2);
				{
				setState(320);
				((ListExtensionNameContext)_localctx).p_2_1 = match(ExtensionName);
				 ((ListExtensionNameContext)_localctx).result =  new stella.Absyn.ListExtensionName(); _localctx.result.addLast(((ListExtensionNameContext)_localctx).p_2_1.getText()); 
				}
				break;
			case 3:
				enterOuterAlt(_localctx, 3);
				{
				setState(322);
				((ListExtensionNameContext)_localctx).p_3_1 = match(ExtensionName);
				setState(323);
				match(Surrogate_id_SYMB_1);
				setState(324);
				((ListExtensionNameContext)_localctx).p_3_3 = listExtensionName();
				 ((ListExtensionNameContext)_localctx).result =  ((ListExtensionNameContext)_localctx).p_3_3.result; _localctx.result.addFirst(((ListExtensionNameContext)_localctx).p_3_1.getText()); 
				}
				break;
			}
		}
		catch (RecognitionException re) {
			_localctx.exception = re;
			_errHandler.reportError(this, re);
			_errHandler.recover(this, re);
		}
		finally {
			exitRule();
		}
		return _localctx;
	}

	public static class ListExtensionContext extends ParserRuleContext {
		public stella.Absyn.ListExtension result;
		public ListExtensionContext p_2_1;
		public ExtensionContext p_2_2;
		public TerminalNode Surrogate_id_SYMB_0() { return getToken(stellaParser.Surrogate_id_SYMB_0, 0); }
		public ListExtensionContext listExtension() {
			return getRuleContext(ListExtensionContext.class,0);
		}
		public ExtensionContext extension() {
			return getRuleContext(ExtensionContext.class,0);
		}
		public ListExtensionContext(ParserRuleContext parent, int invokingState) {
			super(parent, invokingState);
		}
		@Override public int getRuleIndex() { return RULE_listExtension; }
		@Override
		public void enterRule(ParseTreeListener listener) {
			if ( listener instanceof stellaParserListener ) ((stellaParserListener)listener).enterListExtension(this);
		}
		@Override
		public void exitRule(ParseTreeListener listener) {
			if ( listener instanceof stellaParserListener ) ((stellaParserListener)listener).exitListExtension(this);
		}
	}

	public final ListExtensionContext listExtension() throws RecognitionException {
		return listExtension(0);
	}

	private ListExtensionContext listExtension(int _p) throws RecognitionException {
		ParserRuleContext _parentctx = _ctx;
		int _parentState = getState();
		ListExtensionContext _localctx = new ListExtensionContext(_ctx, _parentState);
		ListExtensionContext _prevctx = _localctx;
		int _startState = 84;
		enterRecursionRule(_localctx, 84, RULE_listExtension, _p);
		try {
			int _alt;
			enterOuterAlt(_localctx, 1);
			{
			{
			 ((ListExtensionContext)_localctx).result =  new stella.Absyn.ListExtension(); 
			}
			_ctx.stop = _input.LT(-1);
			setState(339);
			_errHandler.sync(this);
			_alt = getInterpreter().adaptivePredict(_input,1,_ctx);
			while ( _alt!=2 && _alt!=org.antlr.v4.runtime.atn.ATN.INVALID_ALT_NUMBER ) {
				if ( _alt==1 ) {
					if ( _parseListeners!=null ) triggerExitRuleEvent();
					_prevctx = _localctx;
					{
					{
					_localctx = new ListExtensionContext(_parentctx, _parentState);
					_localctx.p_2_1 = _prevctx;
					_localctx.p_2_1 = _prevctx;
					pushNewRecursionContext(_localctx, _startState, RULE_listExtension);
					setState(332);
					if (!(precpred(_ctx, 1))) throw new FailedPredicateException(this, "precpred(_ctx, 1)");
					setState(333);
					((ListExtensionContext)_localctx).p_2_2 = extension();
					setState(334);
					match(Surrogate_id_SYMB_0);
					 ((ListExtensionContext)_localctx).result =  ((ListExtensionContext)_localctx).p_2_1.result; _localctx.result.addLast(((ListExtensionContext)_localctx).p_2_2.result); 
					}
					} 
				}
				setState(341);
				_errHandler.sync(this);
				_alt = getInterpreter().adaptivePredict(_input,1,_ctx);
			}
			}
		}
		catch (RecognitionException re) {
			_localctx.exception = re;
			_errHandler.reportError(this, re);
			_errHandler.recover(this, re);
		}
		finally {
			unrollRecursionContexts(_parentctx);
		}
		return _localctx;
	}

	public static class DeclContext extends ParserRuleContext {
		public stella.Absyn.Decl result;
		public ListAnnotationContext p_1_1;
		public Token p_1_3;
		public ListParamDeclContext p_1_5;
		public ReturnTypeContext p_1_7;
		public ThrowTypeContext p_1_8;
		public ListDeclContext p_1_10;
		public ExprContext p_1_12;
		public Token p_2_2;
		public TypeContext p_2_4;
		public TerminalNode Surrogate_id_SYMB_38() { return getToken(stellaParser.Surrogate_id_SYMB_38, 0); }
		public TerminalNode Surrogate_id_SYMB_2() { return getToken(stellaParser.Surrogate_id_SYMB_2, 0); }
		public TerminalNode Surrogate_id_SYMB_3() { return getToken(stellaParser.Surrogate_id_SYMB_3, 0); }
		public TerminalNode Surrogate_id_SYMB_4() { return getToken(stellaParser.Surrogate_id_SYMB_4, 0); }
		public TerminalNode Surrogate_id_SYMB_49() { return getToken(stellaParser.Surrogate_id_SYMB_49, 0); }
		public TerminalNode Surrogate_id_SYMB_0() { return getToken(stellaParser.Surrogate_id_SYMB_0, 0); }
		public TerminalNode Surrogate_id_SYMB_5() { return getToken(stellaParser.Surrogate_id_SYMB_5, 0); }
		public ListAnnotationContext listAnnotation() {
			return getRuleContext(ListAnnotationContext.class,0);
		}
		public TerminalNode StellaIdent() { return getToken(stellaParser.StellaIdent, 0); }
		public ListParamDeclContext listParamDecl() {
			return getRuleContext(ListParamDeclContext.class,0);
		}
		public ReturnTypeContext returnType() {
			return getRuleContext(ReturnTypeContext.class,0);
		}
		public ThrowTypeContext throwType() {
			return getRuleContext(ThrowTypeContext.class,0);
		}
		public ListDeclContext listDecl() {
			return getRuleContext(ListDeclContext.class,0);
		}
		public ExprContext expr() {
			return getRuleContext(ExprContext.class,0);
		}
		public TerminalNode Surrogate_id_SYMB_55() { return getToken(stellaParser.Surrogate_id_SYMB_55, 0); }
		public TerminalNode Surrogate_id_SYMB_6() { return getToken(stellaParser.Surrogate_id_SYMB_6, 0); }
		public TypeContext type() {
			return getRuleContext(TypeContext.class,0);
		}
		public DeclContext(ParserRuleContext parent, int invokingState) {
			super(parent, invokingState);
		}
		@Override public int getRuleIndex() { return RULE_decl; }
		@Override
		public void enterRule(ParseTreeListener listener) {
			if ( listener instanceof stellaParserListener ) ((stellaParserListener)listener).enterDecl(this);
		}
		@Override
		public void exitRule(ParseTreeListener listener) {
			if ( listener instanceof stellaParserListener ) ((stellaParserListener)listener).exitDecl(this);
		}
	}

	public final DeclContext decl() throws RecognitionException {
		DeclContext _localctx = new DeclContext(_ctx, getState());
		enterRule(_localctx, 86, RULE_decl);
		try {
			setState(364);
			_errHandler.sync(this);
			switch ( getInterpreter().adaptivePredict(_input,2,_ctx) ) {
			case 1:
				enterOuterAlt(_localctx, 1);
				{
				setState(342);
				((DeclContext)_localctx).p_1_1 = listAnnotation(0);
				setState(343);
				match(Surrogate_id_SYMB_38);
				setState(344);
				((DeclContext)_localctx).p_1_3 = match(StellaIdent);
				setState(345);
				match(Surrogate_id_SYMB_2);
				setState(346);
				((DeclContext)_localctx).p_1_5 = listParamDecl();
				setState(347);
				match(Surrogate_id_SYMB_3);
				setState(348);
				((DeclContext)_localctx).p_1_7 = returnType();
				setState(349);
				((DeclContext)_localctx).p_1_8 = throwType();
				setState(350);
				match(Surrogate_id_SYMB_4);
				setState(351);
				((DeclContext)_localctx).p_1_10 = listDecl(0);
				setState(352);
				match(Surrogate_id_SYMB_49);
				setState(353);
				((DeclContext)_localctx).p_1_12 = expr();
				setState(354);
				match(Surrogate_id_SYMB_0);
				setState(355);
				match(Surrogate_id_SYMB_5);
				 ((DeclContext)_localctx).result =  new stella.Absyn.DeclFun(((DeclContext)_localctx).p_1_1.result,((DeclContext)_localctx).p_1_3.getText(),((DeclContext)_localctx).p_1_5.result,((DeclContext)_localctx).p_1_7.result,((DeclContext)_localctx).p_1_8.result,((DeclContext)_localctx).p_1_10.result,((DeclContext)_localctx).p_1_12.result); 
				}
				break;
			case 2:
				enterOuterAlt(_localctx, 2);
				{
				setState(358);
				match(Surrogate_id_SYMB_55);
				setState(359);
				((DeclContext)_localctx).p_2_2 = match(StellaIdent);
				setState(360);
				match(Surrogate_id_SYMB_6);
				setState(361);
				((DeclContext)_localctx).p_2_4 = type();
				 ((DeclContext)_localctx).result =  new stella.Absyn.DeclTypeAlias(((DeclContext)_localctx).p_2_2.getText(),((DeclContext)_localctx).p_2_4.result); 
				}
				break;
			}
		}
		catch (RecognitionException re) {
			_localctx.exception = re;
			_errHandler.reportError(this, re);
			_errHandler.recover(this, re);
		}
		finally {
			exitRule();
		}
		return _localctx;
	}

	public static class ListDeclContext extends ParserRuleContext {
		public stella.Absyn.ListDecl result;
		public ListDeclContext p_2_1;
		public DeclContext p_2_2;
		public ListDeclContext listDecl() {
			return getRuleContext(ListDeclContext.class,0);
		}
		public DeclContext decl() {
			return getRuleContext(DeclContext.class,0);
		}
		public ListDeclContext(ParserRuleContext parent, int invokingState) {
			super(parent, invokingState);
		}
		@Override public int getRuleIndex() { return RULE_listDecl; }
		@Override
		public void enterRule(ParseTreeListener listener) {
			if ( listener instanceof stellaParserListener ) ((stellaParserListener)listener).enterListDecl(this);
		}
		@Override
		public void exitRule(ParseTreeListener listener) {
			if ( listener instanceof stellaParserListener ) ((stellaParserListener)listener).exitListDecl(this);
		}
	}

	public final ListDeclContext listDecl() throws RecognitionException {
		return listDecl(0);
	}

	private ListDeclContext listDecl(int _p) throws RecognitionException {
		ParserRuleContext _parentctx = _ctx;
		int _parentState = getState();
		ListDeclContext _localctx = new ListDeclContext(_ctx, _parentState);
		ListDeclContext _prevctx = _localctx;
		int _startState = 88;
		enterRecursionRule(_localctx, 88, RULE_listDecl, _p);
		try {
			int _alt;
			enterOuterAlt(_localctx, 1);
			{
			{
			 ((ListDeclContext)_localctx).result =  new stella.Absyn.ListDecl(); 
			}
			_ctx.stop = _input.LT(-1);
			setState(375);
			_errHandler.sync(this);
			_alt = getInterpreter().adaptivePredict(_input,3,_ctx);
			while ( _alt!=2 && _alt!=org.antlr.v4.runtime.atn.ATN.INVALID_ALT_NUMBER ) {
				if ( _alt==1 ) {
					if ( _parseListeners!=null ) triggerExitRuleEvent();
					_prevctx = _localctx;
					{
					{
					_localctx = new ListDeclContext(_parentctx, _parentState);
					_localctx.p_2_1 = _prevctx;
					_localctx.p_2_1 = _prevctx;
					pushNewRecursionContext(_localctx, _startState, RULE_listDecl);
					setState(369);
					if (!(precpred(_ctx, 1))) throw new FailedPredicateException(this, "precpred(_ctx, 1)");
					setState(370);
					((ListDeclContext)_localctx).p_2_2 = decl();
					 ((ListDeclContext)_localctx).result =  ((ListDeclContext)_localctx).p_2_1.result; _localctx.result.addLast(((ListDeclContext)_localctx).p_2_2.result); 
					}
					} 
				}
				setState(377);
				_errHandler.sync(this);
				_alt = getInterpreter().adaptivePredict(_input,3,_ctx);
			}
			}
		}
		catch (RecognitionException re) {
			_localctx.exception = re;
			_errHandler.reportError(this, re);
			_errHandler.recover(this, re);
		}
		finally {
			unrollRecursionContexts(_parentctx);
		}
		return _localctx;
	}

	public static class LocalDeclContext extends ParserRuleContext {
		public stella.Absyn.LocalDecl result;
		public DeclContext p_1_1;
		public DeclContext decl() {
			return getRuleContext(DeclContext.class,0);
		}
		public LocalDeclContext(ParserRuleContext parent, int invokingState) {
			super(parent, invokingState);
		}
		@Override public int getRuleIndex() { return RULE_localDecl; }
		@Override
		public void enterRule(ParseTreeListener listener) {
			if ( listener instanceof stellaParserListener ) ((stellaParserListener)listener).enterLocalDecl(this);
		}
		@Override
		public void exitRule(ParseTreeListener listener) {
			if ( listener instanceof stellaParserListener ) ((stellaParserListener)listener).exitLocalDecl(this);
		}
	}

	public final LocalDeclContext localDecl() throws RecognitionException {
		LocalDeclContext _localctx = new LocalDeclContext(_ctx, getState());
		enterRule(_localctx, 90, RULE_localDecl);
		try {
			enterOuterAlt(_localctx, 1);
			{
			setState(378);
			((LocalDeclContext)_localctx).p_1_1 = decl();
			 ((LocalDeclContext)_localctx).result =  new stella.Absyn.ALocalDecl(((LocalDeclContext)_localctx).p_1_1.result); 
			}
		}
		catch (RecognitionException re) {
			_localctx.exception = re;
			_errHandler.reportError(this, re);
			_errHandler.recover(this, re);
		}
		finally {
			exitRule();
		}
		return _localctx;
	}

	public static class ListLocalDeclContext extends ParserRuleContext {
		public stella.Absyn.ListLocalDecl result;
		public ListLocalDeclContext p_2_1;
		public LocalDeclContext p_2_2;
		public TerminalNode Surrogate_id_SYMB_0() { return getToken(stellaParser.Surrogate_id_SYMB_0, 0); }
		public ListLocalDeclContext listLocalDecl() {
			return getRuleContext(ListLocalDeclContext.class,0);
		}
		public LocalDeclContext localDecl() {
			return getRuleContext(LocalDeclContext.class,0);
		}
		public ListLocalDeclContext(ParserRuleContext parent, int invokingState) {
			super(parent, invokingState);
		}
		@Override public int getRuleIndex() { return RULE_listLocalDecl; }
		@Override
		public void enterRule(ParseTreeListener listener) {
			if ( listener instanceof stellaParserListener ) ((stellaParserListener)listener).enterListLocalDecl(this);
		}
		@Override
		public void exitRule(ParseTreeListener listener) {
			if ( listener instanceof stellaParserListener ) ((stellaParserListener)listener).exitListLocalDecl(this);
		}
	}

	public final ListLocalDeclContext listLocalDecl() throws RecognitionException {
		return listLocalDecl(0);
	}

	private ListLocalDeclContext listLocalDecl(int _p) throws RecognitionException {
		ParserRuleContext _parentctx = _ctx;
		int _parentState = getState();
		ListLocalDeclContext _localctx = new ListLocalDeclContext(_ctx, _parentState);
		ListLocalDeclContext _prevctx = _localctx;
		int _startState = 92;
		enterRecursionRule(_localctx, 92, RULE_listLocalDecl, _p);
		try {
			int _alt;
			enterOuterAlt(_localctx, 1);
			{
			{
			 ((ListLocalDeclContext)_localctx).result =  new stella.Absyn.ListLocalDecl(); 
			}
			_ctx.stop = _input.LT(-1);
			setState(391);
			_errHandler.sync(this);
			_alt = getInterpreter().adaptivePredict(_input,4,_ctx);
			while ( _alt!=2 && _alt!=org.antlr.v4.runtime.atn.ATN.INVALID_ALT_NUMBER ) {
				if ( _alt==1 ) {
					if ( _parseListeners!=null ) triggerExitRuleEvent();
					_prevctx = _localctx;
					{
					{
					_localctx = new ListLocalDeclContext(_parentctx, _parentState);
					_localctx.p_2_1 = _prevctx;
					_localctx.p_2_1 = _prevctx;
					pushNewRecursionContext(_localctx, _startState, RULE_listLocalDecl);
					setState(384);
					if (!(precpred(_ctx, 1))) throw new FailedPredicateException(this, "precpred(_ctx, 1)");
					setState(385);
					((ListLocalDeclContext)_localctx).p_2_2 = localDecl();
					setState(386);
					match(Surrogate_id_SYMB_0);
					 ((ListLocalDeclContext)_localctx).result =  ((ListLocalDeclContext)_localctx).p_2_1.result; _localctx.result.addLast(((ListLocalDeclContext)_localctx).p_2_2.result); 
					}
					} 
				}
				setState(393);
				_errHandler.sync(this);
				_alt = getInterpreter().adaptivePredict(_input,4,_ctx);
			}
			}
		}
		catch (RecognitionException re) {
			_localctx.exception = re;
			_errHandler.reportError(this, re);
			_errHandler.recover(this, re);
		}
		finally {
			unrollRecursionContexts(_parentctx);
		}
		return _localctx;
	}

	public static class AnnotationContext extends ParserRuleContext {
		public stella.Absyn.Annotation result;
		public TerminalNode Surrogate_id_SYMB_42() { return getToken(stellaParser.Surrogate_id_SYMB_42, 0); }
		public AnnotationContext(ParserRuleContext parent, int invokingState) {
			super(parent, invokingState);
		}
		@Override public int getRuleIndex() { return RULE_annotation; }
		@Override
		public void enterRule(ParseTreeListener listener) {
			if ( listener instanceof stellaParserListener ) ((stellaParserListener)listener).enterAnnotation(this);
		}
		@Override
		public void exitRule(ParseTreeListener listener) {
			if ( listener instanceof stellaParserListener ) ((stellaParserListener)listener).exitAnnotation(this);
		}
	}

	public final AnnotationContext annotation() throws RecognitionException {
		AnnotationContext _localctx = new AnnotationContext(_ctx, getState());
		enterRule(_localctx, 94, RULE_annotation);
		try {
			enterOuterAlt(_localctx, 1);
			{
			setState(394);
			match(Surrogate_id_SYMB_42);
			 ((AnnotationContext)_localctx).result =  new stella.Absyn.InlineAnnotation(); 
			}
		}
		catch (RecognitionException re) {
			_localctx.exception = re;
			_errHandler.reportError(this, re);
			_errHandler.recover(this, re);
		}
		finally {
			exitRule();
		}
		return _localctx;
	}

	public static class ListAnnotationContext extends ParserRuleContext {
		public stella.Absyn.ListAnnotation result;
		public ListAnnotationContext p_2_1;
		public AnnotationContext p_2_2;
		public ListAnnotationContext listAnnotation() {
			return getRuleContext(ListAnnotationContext.class,0);
		}
		public AnnotationContext annotation() {
			return getRuleContext(AnnotationContext.class,0);
		}
		public ListAnnotationContext(ParserRuleContext parent, int invokingState) {
			super(parent, invokingState);
		}
		@Override public int getRuleIndex() { return RULE_listAnnotation; }
		@Override
		public void enterRule(ParseTreeListener listener) {
			if ( listener instanceof stellaParserListener ) ((stellaParserListener)listener).enterListAnnotation(this);
		}
		@Override
		public void exitRule(ParseTreeListener listener) {
			if ( listener instanceof stellaParserListener ) ((stellaParserListener)listener).exitListAnnotation(this);
		}
	}

	public final ListAnnotationContext listAnnotation() throws RecognitionException {
		return listAnnotation(0);
	}

	private ListAnnotationContext listAnnotation(int _p) throws RecognitionException {
		ParserRuleContext _parentctx = _ctx;
		int _parentState = getState();
		ListAnnotationContext _localctx = new ListAnnotationContext(_ctx, _parentState);
		ListAnnotationContext _prevctx = _localctx;
		int _startState = 96;
		enterRecursionRule(_localctx, 96, RULE_listAnnotation, _p);
		try {
			int _alt;
			enterOuterAlt(_localctx, 1);
			{
			{
			 ((ListAnnotationContext)_localctx).result =  new stella.Absyn.ListAnnotation(); 
			}
			_ctx.stop = _input.LT(-1);
			setState(406);
			_errHandler.sync(this);
			_alt = getInterpreter().adaptivePredict(_input,5,_ctx);
			while ( _alt!=2 && _alt!=org.antlr.v4.runtime.atn.ATN.INVALID_ALT_NUMBER ) {
				if ( _alt==1 ) {
					if ( _parseListeners!=null ) triggerExitRuleEvent();
					_prevctx = _localctx;
					{
					{
					_localctx = new ListAnnotationContext(_parentctx, _parentState);
					_localctx.p_2_1 = _prevctx;
					_localctx.p_2_1 = _prevctx;
					pushNewRecursionContext(_localctx, _startState, RULE_listAnnotation);
					setState(400);
					if (!(precpred(_ctx, 1))) throw new FailedPredicateException(this, "precpred(_ctx, 1)");
					setState(401);
					((ListAnnotationContext)_localctx).p_2_2 = annotation();
					 ((ListAnnotationContext)_localctx).result =  ((ListAnnotationContext)_localctx).p_2_1.result; _localctx.result.addLast(((ListAnnotationContext)_localctx).p_2_2.result); 
					}
					} 
				}
				setState(408);
				_errHandler.sync(this);
				_alt = getInterpreter().adaptivePredict(_input,5,_ctx);
			}
			}
		}
		catch (RecognitionException re) {
			_localctx.exception = re;
			_errHandler.reportError(this, re);
			_errHandler.recover(this, re);
		}
		finally {
			unrollRecursionContexts(_parentctx);
		}
		return _localctx;
	}

	public static class ParamDeclContext extends ParserRuleContext {
		public stella.Absyn.ParamDecl result;
		public Token p_1_1;
		public TypeContext p_1_3;
		public TerminalNode Surrogate_id_SYMB_7() { return getToken(stellaParser.Surrogate_id_SYMB_7, 0); }
		public TerminalNode StellaIdent() { return getToken(stellaParser.StellaIdent, 0); }
		public TypeContext type() {
			return getRuleContext(TypeContext.class,0);
		}
		public ParamDeclContext(ParserRuleContext parent, int invokingState) {
			super(parent, invokingState);
		}
		@Override public int getRuleIndex() { return RULE_paramDecl; }
		@Override
		public void enterRule(ParseTreeListener listener) {
			if ( listener instanceof stellaParserListener ) ((stellaParserListener)listener).enterParamDecl(this);
		}
		@Override
		public void exitRule(ParseTreeListener listener) {
			if ( listener instanceof stellaParserListener ) ((stellaParserListener)listener).exitParamDecl(this);
		}
	}

	public final ParamDeclContext paramDecl() throws RecognitionException {
		ParamDeclContext _localctx = new ParamDeclContext(_ctx, getState());
		enterRule(_localctx, 98, RULE_paramDecl);
		try {
			enterOuterAlt(_localctx, 1);
			{
			setState(409);
			((ParamDeclContext)_localctx).p_1_1 = match(StellaIdent);
			setState(410);
			match(Surrogate_id_SYMB_7);
			setState(411);
			((ParamDeclContext)_localctx).p_1_3 = type();
			 ((ParamDeclContext)_localctx).result =  new stella.Absyn.AParamDecl(((ParamDeclContext)_localctx).p_1_1.getText(),((ParamDeclContext)_localctx).p_1_3.result); 
			}
		}
		catch (RecognitionException re) {
			_localctx.exception = re;
			_errHandler.reportError(this, re);
			_errHandler.recover(this, re);
		}
		finally {
			exitRule();
		}
		return _localctx;
	}

	public static class ListParamDeclContext extends ParserRuleContext {
		public stella.Absyn.ListParamDecl result;
		public ParamDeclContext p_2_1;
		public ParamDeclContext p_3_1;
		public ListParamDeclContext p_3_3;
		public ParamDeclContext paramDecl() {
			return getRuleContext(ParamDeclContext.class,0);
		}
		public TerminalNode Surrogate_id_SYMB_1() { return getToken(stellaParser.Surrogate_id_SYMB_1, 0); }
		public ListParamDeclContext listParamDecl() {
			return getRuleContext(ListParamDeclContext.class,0);
		}
		public ListParamDeclContext(ParserRuleContext parent, int invokingState) {
			super(parent, invokingState);
		}
		@Override public int getRuleIndex() { return RULE_listParamDecl; }
		@Override
		public void enterRule(ParseTreeListener listener) {
			if ( listener instanceof stellaParserListener ) ((stellaParserListener)listener).enterListParamDecl(this);
		}
		@Override
		public void exitRule(ParseTreeListener listener) {
			if ( listener instanceof stellaParserListener ) ((stellaParserListener)listener).exitListParamDecl(this);
		}
	}

	public final ListParamDeclContext listParamDecl() throws RecognitionException {
		ListParamDeclContext _localctx = new ListParamDeclContext(_ctx, getState());
		enterRule(_localctx, 100, RULE_listParamDecl);
		try {
			setState(423);
			_errHandler.sync(this);
			switch ( getInterpreter().adaptivePredict(_input,6,_ctx) ) {
			case 1:
				enterOuterAlt(_localctx, 1);
				{
				 ((ListParamDeclContext)_localctx).result =  new stella.Absyn.ListParamDecl(); 
				}
				break;
			case 2:
				enterOuterAlt(_localctx, 2);
				{
				setState(415);
				((ListParamDeclContext)_localctx).p_2_1 = paramDecl();
				 ((ListParamDeclContext)_localctx).result =  new stella.Absyn.ListParamDecl(); _localctx.result.addLast(((ListParamDeclContext)_localctx).p_2_1.result); 
				}
				break;
			case 3:
				enterOuterAlt(_localctx, 3);
				{
				setState(418);
				((ListParamDeclContext)_localctx).p_3_1 = paramDecl();
				setState(419);
				match(Surrogate_id_SYMB_1);
				setState(420);
				((ListParamDeclContext)_localctx).p_3_3 = listParamDecl();
				 ((ListParamDeclContext)_localctx).result =  ((ListParamDeclContext)_localctx).p_3_3.result; _localctx.result.addFirst(((ListParamDeclContext)_localctx).p_3_1.result); 
				}
				break;
			}
		}
		catch (RecognitionException re) {
			_localctx.exception = re;
			_errHandler.reportError(this, re);
			_errHandler.recover(this, re);
		}
		finally {
			exitRule();
		}
		return _localctx;
	}

	public static class ReturnTypeContext extends ParserRuleContext {
		public stella.Absyn.ReturnType result;
		public TypeContext p_2_2;
		public TerminalNode Surrogate_id_SYMB_8() { return getToken(stellaParser.Surrogate_id_SYMB_8, 0); }
		public TypeContext type() {
			return getRuleContext(TypeContext.class,0);
		}
		public ReturnTypeContext(ParserRuleContext parent, int invokingState) {
			super(parent, invokingState);
		}
		@Override public int getRuleIndex() { return RULE_returnType; }
		@Override
		public void enterRule(ParseTreeListener listener) {
			if ( listener instanceof stellaParserListener ) ((stellaParserListener)listener).enterReturnType(this);
		}
		@Override
		public void exitRule(ParseTreeListener listener) {
			if ( listener instanceof stellaParserListener ) ((stellaParserListener)listener).exitReturnType(this);
		}
	}

	public final ReturnTypeContext returnType() throws RecognitionException {
		ReturnTypeContext _localctx = new ReturnTypeContext(_ctx, getState());
		enterRule(_localctx, 102, RULE_returnType);
		try {
			setState(430);
			_errHandler.sync(this);
			switch (_input.LA(1)) {
			case EOF:
			case Surrogate_id_SYMB_4:
			case Surrogate_id_SYMB_53:
				enterOuterAlt(_localctx, 1);
				{
				 ((ReturnTypeContext)_localctx).result =  new stella.Absyn.NoReturnType(); 
				}
				break;
			case Surrogate_id_SYMB_8:
				enterOuterAlt(_localctx, 2);
				{
				setState(426);
				match(Surrogate_id_SYMB_8);
				setState(427);
				((ReturnTypeContext)_localctx).p_2_2 = type();
				 ((ReturnTypeContext)_localctx).result =  new stella.Absyn.SomeReturnType(((ReturnTypeContext)_localctx).p_2_2.result); 
				}
				break;
			default:
				throw new NoViableAltException(this);
			}
		}
		catch (RecognitionException re) {
			_localctx.exception = re;
			_errHandler.reportError(this, re);
			_errHandler.recover(this, re);
		}
		finally {
			exitRule();
		}
		return _localctx;
	}

	public static class ThrowTypeContext extends ParserRuleContext {
		public stella.Absyn.ThrowType result;
		public ListTypeContext p_2_2;
		public TerminalNode Surrogate_id_SYMB_53() { return getToken(stellaParser.Surrogate_id_SYMB_53, 0); }
		public ListTypeContext listType() {
			return getRuleContext(ListTypeContext.class,0);
		}
		public ThrowTypeContext(ParserRuleContext parent, int invokingState) {
			super(parent, invokingState);
		}
		@Override public int getRuleIndex() { return RULE_throwType; }
		@Override
		public void enterRule(ParseTreeListener listener) {
			if ( listener instanceof stellaParserListener ) ((stellaParserListener)listener).enterThrowType(this);
		}
		@Override
		public void exitRule(ParseTreeListener listener) {
			if ( listener instanceof stellaParserListener ) ((stellaParserListener)listener).exitThrowType(this);
		}
	}

	public final ThrowTypeContext throwType() throws RecognitionException {
		ThrowTypeContext _localctx = new ThrowTypeContext(_ctx, getState());
		enterRule(_localctx, 104, RULE_throwType);
		try {
			setState(437);
			_errHandler.sync(this);
			switch (_input.LA(1)) {
			case EOF:
			case Surrogate_id_SYMB_4:
				enterOuterAlt(_localctx, 1);
				{
				 ((ThrowTypeContext)_localctx).result =  new stella.Absyn.NoThrowType(); 
				}
				break;
			case Surrogate_id_SYMB_53:
				enterOuterAlt(_localctx, 2);
				{
				setState(433);
				match(Surrogate_id_SYMB_53);
				setState(434);
				((ThrowTypeContext)_localctx).p_2_2 = listType();
				 ((ThrowTypeContext)_localctx).result =  new stella.Absyn.SomeThrowType(((ThrowTypeContext)_localctx).p_2_2.result); 
				}
				break;
			default:
				throw new NoViableAltException(this);
			}
		}
		catch (RecognitionException re) {
			_localctx.exception = re;
			_errHandler.reportError(this, re);
			_errHandler.recover(this, re);
		}
		finally {
			exitRule();
		}
		return _localctx;
	}

	public static class ExprContext extends ParserRuleContext {
		public stella.Absyn.Expr result;
		public ExprContext p_1_2;
		public ExprContext p_1_4;
		public ExprContext p_1_6;
		public Token p_2_2;
		public ExprContext p_2_4;
		public ExprContext p_2_6;
		public Expr1Context p_3_1;
		public TerminalNode Surrogate_id_SYMB_40() { return getToken(stellaParser.Surrogate_id_SYMB_40, 0); }
		public TerminalNode Surrogate_id_SYMB_52() { return getToken(stellaParser.Surrogate_id_SYMB_52, 0); }
		public TerminalNode Surrogate_id_SYMB_34() { return getToken(stellaParser.Surrogate_id_SYMB_34, 0); }
		public List<ExprContext> expr() {
			return getRuleContexts(ExprContext.class);
		}
		public ExprContext expr(int i) {
			return getRuleContext(ExprContext.class,i);
		}
		public TerminalNode Surrogate_id_SYMB_44() { return getToken(stellaParser.Surrogate_id_SYMB_44, 0); }
		public TerminalNode Surrogate_id_SYMB_6() { return getToken(stellaParser.Surrogate_id_SYMB_6, 0); }
		public TerminalNode Surrogate_id_SYMB_41() { return getToken(stellaParser.Surrogate_id_SYMB_41, 0); }
		public TerminalNode StellaIdent() { return getToken(stellaParser.StellaIdent, 0); }
		public Expr1Context expr1() {
			return getRuleContext(Expr1Context.class,0);
		}
		public ExprContext(ParserRuleContext parent, int invokingState) {
			super(parent, invokingState);
		}
		@Override public int getRuleIndex() { return RULE_expr; }
		@Override
		public void enterRule(ParseTreeListener listener) {
			if ( listener instanceof stellaParserListener ) ((stellaParserListener)listener).enterExpr(this);
		}
		@Override
		public void exitRule(ParseTreeListener listener) {
			if ( listener instanceof stellaParserListener ) ((stellaParserListener)listener).exitExpr(this);
		}
	}

	public final ExprContext expr() throws RecognitionException {
		ExprContext _localctx = new ExprContext(_ctx, getState());
		enterRule(_localctx, 106, RULE_expr);
		try {
			setState(458);
			_errHandler.sync(this);
			switch (_input.LA(1)) {
			case Surrogate_id_SYMB_40:
				enterOuterAlt(_localctx, 1);
				{
				setState(439);
				match(Surrogate_id_SYMB_40);
				setState(440);
				((ExprContext)_localctx).p_1_2 = expr();
				setState(441);
				match(Surrogate_id_SYMB_52);
				setState(442);
				((ExprContext)_localctx).p_1_4 = expr();
				setState(443);
				match(Surrogate_id_SYMB_34);
				setState(444);
				((ExprContext)_localctx).p_1_6 = expr();
				 ((ExprContext)_localctx).result =  new stella.Absyn.If(((ExprContext)_localctx).p_1_2.result,((ExprContext)_localctx).p_1_4.result,((ExprContext)_localctx).p_1_6.result); 
				}
				break;
			case Surrogate_id_SYMB_44:
				enterOuterAlt(_localctx, 2);
				{
				setState(447);
				match(Surrogate_id_SYMB_44);
				setState(448);
				((ExprContext)_localctx).p_2_2 = match(StellaIdent);
				setState(449);
				match(Surrogate_id_SYMB_6);
				setState(450);
				((ExprContext)_localctx).p_2_4 = expr();
				setState(451);
				match(Surrogate_id_SYMB_41);
				setState(452);
				((ExprContext)_localctx).p_2_6 = expr();
				 ((ExprContext)_localctx).result =  new stella.Absyn.Let(((ExprContext)_localctx).p_2_2.getText(),((ExprContext)_localctx).p_2_4.result,((ExprContext)_localctx).p_2_6.result); 
				}
				break;
			case Surrogate_id_SYMB_2:
			case Surrogate_id_SYMB_4:
			case Surrogate_id_SYMB_10:
			case Surrogate_id_SYMB_12:
			case Surrogate_id_SYMB_20:
			case Surrogate_id_SYMB_21:
			case Surrogate_id_SYMB_22:
			case Surrogate_id_SYMB_23:
			case Surrogate_id_SYMB_24:
			case Surrogate_id_SYMB_25:
			case Surrogate_id_SYMB_32:
			case Surrogate_id_SYMB_36:
			case Surrogate_id_SYMB_37:
			case Surrogate_id_SYMB_38:
			case Surrogate_id_SYMB_39:
			case Surrogate_id_SYMB_45:
			case Surrogate_id_SYMB_46:
			case Surrogate_id_SYMB_48:
			case Surrogate_id_SYMB_51:
			case Surrogate_id_SYMB_54:
			case Surrogate_id_SYMB_56:
			case StellaIdent:
			case INTEGER:
				enterOuterAlt(_localctx, 3);
				{
				setState(455);
				((ExprContext)_localctx).p_3_1 = expr1(0);
				 ((ExprContext)_localctx).result =  ((ExprContext)_localctx).p_3_1.result; 
				}
				break;
			default:
				throw new NoViableAltException(this);
			}
		}
		catch (RecognitionException re) {
			_localctx.exception = re;
			_errHandler.reportError(this, re);
			_errHandler.recover(this, re);
		}
		finally {
			exitRule();
		}
		return _localctx;
	}

	public static class ListExprContext extends ParserRuleContext {
		public stella.Absyn.ListExpr result;
		public ExprContext p_2_1;
		public ExprContext p_3_1;
		public ListExprContext p_3_3;
		public ExprContext expr() {
			return getRuleContext(ExprContext.class,0);
		}
		public TerminalNode Surrogate_id_SYMB_1() { return getToken(stellaParser.Surrogate_id_SYMB_1, 0); }
		public ListExprContext listExpr() {
			return getRuleContext(ListExprContext.class,0);
		}
		public ListExprContext(ParserRuleContext parent, int invokingState) {
			super(parent, invokingState);
		}
		@Override public int getRuleIndex() { return RULE_listExpr; }
		@Override
		public void enterRule(ParseTreeListener listener) {
			if ( listener instanceof stellaParserListener ) ((stellaParserListener)listener).enterListExpr(this);
		}
		@Override
		public void exitRule(ParseTreeListener listener) {
			if ( listener instanceof stellaParserListener ) ((stellaParserListener)listener).exitListExpr(this);
		}
	}

	public final ListExprContext listExpr() throws RecognitionException {
		ListExprContext _localctx = new ListExprContext(_ctx, getState());
		enterRule(_localctx, 108, RULE_listExpr);
		try {
			setState(469);
			_errHandler.sync(this);
			switch ( getInterpreter().adaptivePredict(_input,10,_ctx) ) {
			case 1:
				enterOuterAlt(_localctx, 1);
				{
				 ((ListExprContext)_localctx).result =  new stella.Absyn.ListExpr(); 
				}
				break;
			case 2:
				enterOuterAlt(_localctx, 2);
				{
				setState(461);
				((ListExprContext)_localctx).p_2_1 = expr();
				 ((ListExprContext)_localctx).result =  new stella.Absyn.ListExpr(); _localctx.result.addLast(((ListExprContext)_localctx).p_2_1.result); 
				}
				break;
			case 3:
				enterOuterAlt(_localctx, 3);
				{
				setState(464);
				((ListExprContext)_localctx).p_3_1 = expr();
				setState(465);
				match(Surrogate_id_SYMB_1);
				setState(466);
				((ListExprContext)_localctx).p_3_3 = listExpr();
				 ((ListExprContext)_localctx).result =  ((ListExprContext)_localctx).p_3_3.result; _localctx.result.addFirst(((ListExprContext)_localctx).p_3_1.result); 
				}
				break;
			}
		}
		catch (RecognitionException re) {
			_localctx.exception = re;
			_errHandler.reportError(this, re);
			_errHandler.recover(this, re);
		}
		finally {
			exitRule();
		}
		return _localctx;
	}

	public static class MatchCaseContext extends ParserRuleContext {
		public stella.Absyn.MatchCase result;
		public PatternContext p_1_1;
		public ExprContext p_1_3;
		public TerminalNode Surrogate_id_SYMB_9() { return getToken(stellaParser.Surrogate_id_SYMB_9, 0); }
		public PatternContext pattern() {
			return getRuleContext(PatternContext.class,0);
		}
		public ExprContext expr() {
			return getRuleContext(ExprContext.class,0);
		}
		public MatchCaseContext(ParserRuleContext parent, int invokingState) {
			super(parent, invokingState);
		}
		@Override public int getRuleIndex() { return RULE_matchCase; }
		@Override
		public void enterRule(ParseTreeListener listener) {
			if ( listener instanceof stellaParserListener ) ((stellaParserListener)listener).enterMatchCase(this);
		}
		@Override
		public void exitRule(ParseTreeListener listener) {
			if ( listener instanceof stellaParserListener ) ((stellaParserListener)listener).exitMatchCase(this);
		}
	}

	public final MatchCaseContext matchCase() throws RecognitionException {
		MatchCaseContext _localctx = new MatchCaseContext(_ctx, getState());
		enterRule(_localctx, 110, RULE_matchCase);
		try {
			enterOuterAlt(_localctx, 1);
			{
			setState(471);
			((MatchCaseContext)_localctx).p_1_1 = pattern();
			setState(472);
			match(Surrogate_id_SYMB_9);
			setState(473);
			((MatchCaseContext)_localctx).p_1_3 = expr();
			 ((MatchCaseContext)_localctx).result =  new stella.Absyn.AMatchCase(((MatchCaseContext)_localctx).p_1_1.result,((MatchCaseContext)_localctx).p_1_3.result); 
			}
		}
		catch (RecognitionException re) {
			_localctx.exception = re;
			_errHandler.reportError(this, re);
			_errHandler.recover(this, re);
		}
		finally {
			exitRule();
		}
		return _localctx;
	}

	public static class ListMatchCaseContext extends ParserRuleContext {
		public stella.Absyn.ListMatchCase result;
		public MatchCaseContext p_2_1;
		public MatchCaseContext p_3_1;
		public ListMatchCaseContext p_3_3;
		public MatchCaseContext matchCase() {
			return getRuleContext(MatchCaseContext.class,0);
		}
		public TerminalNode Surrogate_id_SYMB_0() { return getToken(stellaParser.Surrogate_id_SYMB_0, 0); }
		public ListMatchCaseContext listMatchCase() {
			return getRuleContext(ListMatchCaseContext.class,0);
		}
		public ListMatchCaseContext(ParserRuleContext parent, int invokingState) {
			super(parent, invokingState);
		}
		@Override public int getRuleIndex() { return RULE_listMatchCase; }
		@Override
		public void enterRule(ParseTreeListener listener) {
			if ( listener instanceof stellaParserListener ) ((stellaParserListener)listener).enterListMatchCase(this);
		}
		@Override
		public void exitRule(ParseTreeListener listener) {
			if ( listener instanceof stellaParserListener ) ((stellaParserListener)listener).exitListMatchCase(this);
		}
	}

	public final ListMatchCaseContext listMatchCase() throws RecognitionException {
		ListMatchCaseContext _localctx = new ListMatchCaseContext(_ctx, getState());
		enterRule(_localctx, 112, RULE_listMatchCase);
		try {
			setState(485);
			_errHandler.sync(this);
			switch ( getInterpreter().adaptivePredict(_input,11,_ctx) ) {
			case 1:
				enterOuterAlt(_localctx, 1);
				{
				 ((ListMatchCaseContext)_localctx).result =  new stella.Absyn.ListMatchCase(); 
				}
				break;
			case 2:
				enterOuterAlt(_localctx, 2);
				{
				setState(477);
				((ListMatchCaseContext)_localctx).p_2_1 = matchCase();
				 ((ListMatchCaseContext)_localctx).result =  new stella.Absyn.ListMatchCase(); _localctx.result.addLast(((ListMatchCaseContext)_localctx).p_2_1.result); 
				}
				break;
			case 3:
				enterOuterAlt(_localctx, 3);
				{
				setState(480);
				((ListMatchCaseContext)_localctx).p_3_1 = matchCase();
				setState(481);
				match(Surrogate_id_SYMB_0);
				setState(482);
				((ListMatchCaseContext)_localctx).p_3_3 = listMatchCase();
				 ((ListMatchCaseContext)_localctx).result =  ((ListMatchCaseContext)_localctx).p_3_3.result; _localctx.result.addFirst(((ListMatchCaseContext)_localctx).p_3_1.result); 
				}
				break;
			}
		}
		catch (RecognitionException re) {
			_localctx.exception = re;
			_errHandler.reportError(this, re);
			_errHandler.recover(this, re);
		}
		finally {
			exitRule();
		}
		return _localctx;
	}

	public static class PatternContext extends ParserRuleContext {
		public stella.Absyn.Pattern result;
		public Token p_1_2;
		public PatternContext p_1_4;
		public ListPatternContext p_2_2;
		public ListLabelledPatternContext p_3_3;
		public ListPatternContext p_4_2;
		public PatternContext p_5_3;
		public PatternContext p_5_5;
		public Token p_8_1;
		public PatternContext p_9_3;
		public Token p_10_1;
		public PatternContext p_11_2;
		public TerminalNode Surrogate_id_SYMB_10() { return getToken(stellaParser.Surrogate_id_SYMB_10, 0); }
		public TerminalNode Surrogate_id_SYMB_6() { return getToken(stellaParser.Surrogate_id_SYMB_6, 0); }
		public TerminalNode Surrogate_id_SYMB_11() { return getToken(stellaParser.Surrogate_id_SYMB_11, 0); }
		public TerminalNode StellaIdent() { return getToken(stellaParser.StellaIdent, 0); }
		public List<PatternContext> pattern() {
			return getRuleContexts(PatternContext.class);
		}
		public PatternContext pattern(int i) {
			return getRuleContext(PatternContext.class,i);
		}
		public TerminalNode Surrogate_id_SYMB_4() { return getToken(stellaParser.Surrogate_id_SYMB_4, 0); }
		public TerminalNode Surrogate_id_SYMB_5() { return getToken(stellaParser.Surrogate_id_SYMB_5, 0); }
		public ListPatternContext listPattern() {
			return getRuleContext(ListPatternContext.class,0);
		}
		public TerminalNode Surrogate_id_SYMB_48() { return getToken(stellaParser.Surrogate_id_SYMB_48, 0); }
		public ListLabelledPatternContext listLabelledPattern() {
			return getRuleContext(ListLabelledPatternContext.class,0);
		}
		public TerminalNode Surrogate_id_SYMB_12() { return getToken(stellaParser.Surrogate_id_SYMB_12, 0); }
		public TerminalNode Surrogate_id_SYMB_13() { return getToken(stellaParser.Surrogate_id_SYMB_13, 0); }
		public TerminalNode Surrogate_id_SYMB_32() { return getToken(stellaParser.Surrogate_id_SYMB_32, 0); }
		public TerminalNode Surrogate_id_SYMB_2() { return getToken(stellaParser.Surrogate_id_SYMB_2, 0); }
		public TerminalNode Surrogate_id_SYMB_1() { return getToken(stellaParser.Surrogate_id_SYMB_1, 0); }
		public TerminalNode Surrogate_id_SYMB_3() { return getToken(stellaParser.Surrogate_id_SYMB_3, 0); }
		public TerminalNode Surrogate_id_SYMB_36() { return getToken(stellaParser.Surrogate_id_SYMB_36, 0); }
		public TerminalNode Surrogate_id_SYMB_54() { return getToken(stellaParser.Surrogate_id_SYMB_54, 0); }
		public TerminalNode INTEGER() { return getToken(stellaParser.INTEGER, 0); }
		public TerminalNode Surrogate_id_SYMB_51() { return getToken(stellaParser.Surrogate_id_SYMB_51, 0); }
		public PatternContext(ParserRuleContext parent, int invokingState) {
			super(parent, invokingState);
		}
		@Override public int getRuleIndex() { return RULE_pattern; }
		@Override
		public void enterRule(ParseTreeListener listener) {
			if ( listener instanceof stellaParserListener ) ((stellaParserListener)listener).enterPattern(this);
		}
		@Override
		public void exitRule(ParseTreeListener listener) {
			if ( listener instanceof stellaParserListener ) ((stellaParserListener)listener).exitPattern(this);
		}
	}

	public final PatternContext pattern() throws RecognitionException {
		PatternContext _localctx = new PatternContext(_ctx, getState());
		enterRule(_localctx, 114, RULE_pattern);
		try {
			setState(537);
			_errHandler.sync(this);
			switch (_input.LA(1)) {
			case Surrogate_id_SYMB_10:
				enterOuterAlt(_localctx, 1);
				{
				setState(487);
				match(Surrogate_id_SYMB_10);
				setState(488);
				((PatternContext)_localctx).p_1_2 = match(StellaIdent);
				setState(489);
				match(Surrogate_id_SYMB_6);
				setState(490);
				((PatternContext)_localctx).p_1_4 = pattern();
				setState(491);
				match(Surrogate_id_SYMB_11);
				 ((PatternContext)_localctx).result =  new stella.Absyn.PatternVariant(((PatternContext)_localctx).p_1_2.getText(),((PatternContext)_localctx).p_1_4.result); 
				}
				break;
			case Surrogate_id_SYMB_4:
				enterOuterAlt(_localctx, 2);
				{
				setState(494);
				match(Surrogate_id_SYMB_4);
				setState(495);
				((PatternContext)_localctx).p_2_2 = listPattern();
				setState(496);
				match(Surrogate_id_SYMB_5);
				 ((PatternContext)_localctx).result =  new stella.Absyn.PatternTuple(((PatternContext)_localctx).p_2_2.result); 
				}
				break;
			case Surrogate_id_SYMB_48:
				enterOuterAlt(_localctx, 3);
				{
				setState(499);
				match(Surrogate_id_SYMB_48);
				setState(500);
				match(Surrogate_id_SYMB_4);
				setState(501);
				((PatternContext)_localctx).p_3_3 = listLabelledPattern();
				setState(502);
				match(Surrogate_id_SYMB_5);
				 ((PatternContext)_localctx).result =  new stella.Absyn.PatternRecord(((PatternContext)_localctx).p_3_3.result); 
				}
				break;
			case Surrogate_id_SYMB_12:
				enterOuterAlt(_localctx, 4);
				{
				setState(505);
				match(Surrogate_id_SYMB_12);
				setState(506);
				((PatternContext)_localctx).p_4_2 = listPattern();
				setState(507);
				match(Surrogate_id_SYMB_13);
				 ((PatternContext)_localctx).result =  new stella.Absyn.PatternList(((PatternContext)_localctx).p_4_2.result); 
				}
				break;
			case Surrogate_id_SYMB_32:
				enterOuterAlt(_localctx, 5);
				{
				setState(510);
				match(Surrogate_id_SYMB_32);
				setState(511);
				match(Surrogate_id_SYMB_2);
				setState(512);
				((PatternContext)_localctx).p_5_3 = pattern();
				setState(513);
				match(Surrogate_id_SYMB_1);
				setState(514);
				((PatternContext)_localctx).p_5_5 = pattern();
				setState(515);
				match(Surrogate_id_SYMB_3);
				 ((PatternContext)_localctx).result =  new stella.Absyn.PatternCons(((PatternContext)_localctx).p_5_3.result,((PatternContext)_localctx).p_5_5.result); 
				}
				break;
			case Surrogate_id_SYMB_36:
				enterOuterAlt(_localctx, 6);
				{
				setState(518);
				match(Surrogate_id_SYMB_36);
				 ((PatternContext)_localctx).result =  new stella.Absyn.PatternFalse(); 
				}
				break;
			case Surrogate_id_SYMB_54:
				enterOuterAlt(_localctx, 7);
				{
				setState(520);
				match(Surrogate_id_SYMB_54);
				 ((PatternContext)_localctx).result =  new stella.Absyn.PatternTrue(); 
				}
				break;
			case INTEGER:
				enterOuterAlt(_localctx, 8);
				{
				setState(522);
				((PatternContext)_localctx).p_8_1 = match(INTEGER);
				 ((PatternContext)_localctx).result =  new stella.Absyn.PatternInt(Integer.parseInt(((PatternContext)_localctx).p_8_1.getText())); 
				}
				break;
			case Surrogate_id_SYMB_51:
				enterOuterAlt(_localctx, 9);
				{
				setState(524);
				match(Surrogate_id_SYMB_51);
				setState(525);
				match(Surrogate_id_SYMB_2);
				setState(526);
				((PatternContext)_localctx).p_9_3 = pattern();
				setState(527);
				match(Surrogate_id_SYMB_3);
				 ((PatternContext)_localctx).result =  new stella.Absyn.PatternSucc(((PatternContext)_localctx).p_9_3.result); 
				}
				break;
			case StellaIdent:
				enterOuterAlt(_localctx, 10);
				{
				setState(530);
				((PatternContext)_localctx).p_10_1 = match(StellaIdent);
				 ((PatternContext)_localctx).result =  new stella.Absyn.PatternVar(((PatternContext)_localctx).p_10_1.getText()); 
				}
				break;
			case Surrogate_id_SYMB_2:
				enterOuterAlt(_localctx, 11);
				{
				setState(532);
				match(Surrogate_id_SYMB_2);
				setState(533);
				((PatternContext)_localctx).p_11_2 = pattern();
				setState(534);
				match(Surrogate_id_SYMB_3);
				 ((PatternContext)_localctx).result =  ((PatternContext)_localctx).p_11_2.result; 
				}
				break;
			default:
				throw new NoViableAltException(this);
			}
		}
		catch (RecognitionException re) {
			_localctx.exception = re;
			_errHandler.reportError(this, re);
			_errHandler.recover(this, re);
		}
		finally {
			exitRule();
		}
		return _localctx;
	}

	public static class ListPatternContext extends ParserRuleContext {
		public stella.Absyn.ListPattern result;
		public PatternContext p_2_1;
		public PatternContext p_3_1;
		public ListPatternContext p_3_3;
		public PatternContext pattern() {
			return getRuleContext(PatternContext.class,0);
		}
		public TerminalNode Surrogate_id_SYMB_1() { return getToken(stellaParser.Surrogate_id_SYMB_1, 0); }
		public ListPatternContext listPattern() {
			return getRuleContext(ListPatternContext.class,0);
		}
		public ListPatternContext(ParserRuleContext parent, int invokingState) {
			super(parent, invokingState);
		}
		@Override public int getRuleIndex() { return RULE_listPattern; }
		@Override
		public void enterRule(ParseTreeListener listener) {
			if ( listener instanceof stellaParserListener ) ((stellaParserListener)listener).enterListPattern(this);
		}
		@Override
		public void exitRule(ParseTreeListener listener) {
			if ( listener instanceof stellaParserListener ) ((stellaParserListener)listener).exitListPattern(this);
		}
	}

	public final ListPatternContext listPattern() throws RecognitionException {
		ListPatternContext _localctx = new ListPatternContext(_ctx, getState());
		enterRule(_localctx, 116, RULE_listPattern);
		try {
			setState(548);
			_errHandler.sync(this);
			switch ( getInterpreter().adaptivePredict(_input,13,_ctx) ) {
			case 1:
				enterOuterAlt(_localctx, 1);
				{
				 ((ListPatternContext)_localctx).result =  new stella.Absyn.ListPattern(); 
				}
				break;
			case 2:
				enterOuterAlt(_localctx, 2);
				{
				setState(540);
				((ListPatternContext)_localctx).p_2_1 = pattern();
				 ((ListPatternContext)_localctx).result =  new stella.Absyn.ListPattern(); _localctx.result.addLast(((ListPatternContext)_localctx).p_2_1.result); 
				}
				break;
			case 3:
				enterOuterAlt(_localctx, 3);
				{
				setState(543);
				((ListPatternContext)_localctx).p_3_1 = pattern();
				setState(544);
				match(Surrogate_id_SYMB_1);
				setState(545);
				((ListPatternContext)_localctx).p_3_3 = listPattern();
				 ((ListPatternContext)_localctx).result =  ((ListPatternContext)_localctx).p_3_3.result; _localctx.result.addFirst(((ListPatternContext)_localctx).p_3_1.result); 
				}
				break;
			}
		}
		catch (RecognitionException re) {
			_localctx.exception = re;
			_errHandler.reportError(this, re);
			_errHandler.recover(this, re);
		}
		finally {
			exitRule();
		}
		return _localctx;
	}

	public static class LabelledPatternContext extends ParserRuleContext {
		public stella.Absyn.LabelledPattern result;
		public Token p_1_1;
		public PatternContext p_1_3;
		public TerminalNode Surrogate_id_SYMB_6() { return getToken(stellaParser.Surrogate_id_SYMB_6, 0); }
		public TerminalNode StellaIdent() { return getToken(stellaParser.StellaIdent, 0); }
		public PatternContext pattern() {
			return getRuleContext(PatternContext.class,0);
		}
		public LabelledPatternContext(ParserRuleContext parent, int invokingState) {
			super(parent, invokingState);
		}
		@Override public int getRuleIndex() { return RULE_labelledPattern; }
		@Override
		public void enterRule(ParseTreeListener listener) {
			if ( listener instanceof stellaParserListener ) ((stellaParserListener)listener).enterLabelledPattern(this);
		}
		@Override
		public void exitRule(ParseTreeListener listener) {
			if ( listener instanceof stellaParserListener ) ((stellaParserListener)listener).exitLabelledPattern(this);
		}
	}

	public final LabelledPatternContext labelledPattern() throws RecognitionException {
		LabelledPatternContext _localctx = new LabelledPatternContext(_ctx, getState());
		enterRule(_localctx, 118, RULE_labelledPattern);
		try {
			enterOuterAlt(_localctx, 1);
			{
			setState(550);
			((LabelledPatternContext)_localctx).p_1_1 = match(StellaIdent);
			setState(551);
			match(Surrogate_id_SYMB_6);
			setState(552);
			((LabelledPatternContext)_localctx).p_1_3 = pattern();
			 ((LabelledPatternContext)_localctx).result =  new stella.Absyn.ALabelledPattern(((LabelledPatternContext)_localctx).p_1_1.getText(),((LabelledPatternContext)_localctx).p_1_3.result); 
			}
		}
		catch (RecognitionException re) {
			_localctx.exception = re;
			_errHandler.reportError(this, re);
			_errHandler.recover(this, re);
		}
		finally {
			exitRule();
		}
		return _localctx;
	}

	public static class ListLabelledPatternContext extends ParserRuleContext {
		public stella.Absyn.ListLabelledPattern result;
		public LabelledPatternContext p_2_1;
		public LabelledPatternContext p_3_1;
		public ListLabelledPatternContext p_3_3;
		public LabelledPatternContext labelledPattern() {
			return getRuleContext(LabelledPatternContext.class,0);
		}
		public TerminalNode Surrogate_id_SYMB_1() { return getToken(stellaParser.Surrogate_id_SYMB_1, 0); }
		public ListLabelledPatternContext listLabelledPattern() {
			return getRuleContext(ListLabelledPatternContext.class,0);
		}
		public ListLabelledPatternContext(ParserRuleContext parent, int invokingState) {
			super(parent, invokingState);
		}
		@Override public int getRuleIndex() { return RULE_listLabelledPattern; }
		@Override
		public void enterRule(ParseTreeListener listener) {
			if ( listener instanceof stellaParserListener ) ((stellaParserListener)listener).enterListLabelledPattern(this);
		}
		@Override
		public void exitRule(ParseTreeListener listener) {
			if ( listener instanceof stellaParserListener ) ((stellaParserListener)listener).exitListLabelledPattern(this);
		}
	}

	public final ListLabelledPatternContext listLabelledPattern() throws RecognitionException {
		ListLabelledPatternContext _localctx = new ListLabelledPatternContext(_ctx, getState());
		enterRule(_localctx, 120, RULE_listLabelledPattern);
		try {
			setState(564);
			_errHandler.sync(this);
			switch ( getInterpreter().adaptivePredict(_input,14,_ctx) ) {
			case 1:
				enterOuterAlt(_localctx, 1);
				{
				 ((ListLabelledPatternContext)_localctx).result =  new stella.Absyn.ListLabelledPattern(); 
				}
				break;
			case 2:
				enterOuterAlt(_localctx, 2);
				{
				setState(556);
				((ListLabelledPatternContext)_localctx).p_2_1 = labelledPattern();
				 ((ListLabelledPatternContext)_localctx).result =  new stella.Absyn.ListLabelledPattern(); _localctx.result.addLast(((ListLabelledPatternContext)_localctx).p_2_1.result); 
				}
				break;
			case 3:
				enterOuterAlt(_localctx, 3);
				{
				setState(559);
				((ListLabelledPatternContext)_localctx).p_3_1 = labelledPattern();
				setState(560);
				match(Surrogate_id_SYMB_1);
				setState(561);
				((ListLabelledPatternContext)_localctx).p_3_3 = listLabelledPattern();
				 ((ListLabelledPatternContext)_localctx).result =  ((ListLabelledPatternContext)_localctx).p_3_3.result; _localctx.result.addFirst(((ListLabelledPatternContext)_localctx).p_3_1.result); 
				}
				break;
			}
		}
		catch (RecognitionException re) {
			_localctx.exception = re;
			_errHandler.reportError(this, re);
			_errHandler.recover(this, re);
		}
		finally {
			exitRule();
		}
		return _localctx;
	}

	public static class BindingContext extends ParserRuleContext {
		public stella.Absyn.Binding result;
		public Token p_1_1;
		public ExprContext p_1_3;
		public TerminalNode Surrogate_id_SYMB_6() { return getToken(stellaParser.Surrogate_id_SYMB_6, 0); }
		public TerminalNode StellaIdent() { return getToken(stellaParser.StellaIdent, 0); }
		public ExprContext expr() {
			return getRuleContext(ExprContext.class,0);
		}
		public BindingContext(ParserRuleContext parent, int invokingState) {
			super(parent, invokingState);
		}
		@Override public int getRuleIndex() { return RULE_binding; }
		@Override
		public void enterRule(ParseTreeListener listener) {
			if ( listener instanceof stellaParserListener ) ((stellaParserListener)listener).enterBinding(this);
		}
		@Override
		public void exitRule(ParseTreeListener listener) {
			if ( listener instanceof stellaParserListener ) ((stellaParserListener)listener).exitBinding(this);
		}
	}

	public final BindingContext binding() throws RecognitionException {
		BindingContext _localctx = new BindingContext(_ctx, getState());
		enterRule(_localctx, 122, RULE_binding);
		try {
			enterOuterAlt(_localctx, 1);
			{
			setState(566);
			((BindingContext)_localctx).p_1_1 = match(StellaIdent);
			setState(567);
			match(Surrogate_id_SYMB_6);
			setState(568);
			((BindingContext)_localctx).p_1_3 = expr();
			 ((BindingContext)_localctx).result =  new stella.Absyn.ABinding(((BindingContext)_localctx).p_1_1.getText(),((BindingContext)_localctx).p_1_3.result); 
			}
		}
		catch (RecognitionException re) {
			_localctx.exception = re;
			_errHandler.reportError(this, re);
			_errHandler.recover(this, re);
		}
		finally {
			exitRule();
		}
		return _localctx;
	}

	public static class ListBindingContext extends ParserRuleContext {
		public stella.Absyn.ListBinding result;
		public BindingContext p_2_1;
		public BindingContext p_3_1;
		public ListBindingContext p_3_3;
		public BindingContext binding() {
			return getRuleContext(BindingContext.class,0);
		}
		public TerminalNode Surrogate_id_SYMB_1() { return getToken(stellaParser.Surrogate_id_SYMB_1, 0); }
		public ListBindingContext listBinding() {
			return getRuleContext(ListBindingContext.class,0);
		}
		public ListBindingContext(ParserRuleContext parent, int invokingState) {
			super(parent, invokingState);
		}
		@Override public int getRuleIndex() { return RULE_listBinding; }
		@Override
		public void enterRule(ParseTreeListener listener) {
			if ( listener instanceof stellaParserListener ) ((stellaParserListener)listener).enterListBinding(this);
		}
		@Override
		public void exitRule(ParseTreeListener listener) {
			if ( listener instanceof stellaParserListener ) ((stellaParserListener)listener).exitListBinding(this);
		}
	}

	public final ListBindingContext listBinding() throws RecognitionException {
		ListBindingContext _localctx = new ListBindingContext(_ctx, getState());
		enterRule(_localctx, 124, RULE_listBinding);
		try {
			setState(580);
			_errHandler.sync(this);
			switch ( getInterpreter().adaptivePredict(_input,15,_ctx) ) {
			case 1:
				enterOuterAlt(_localctx, 1);
				{
				 ((ListBindingContext)_localctx).result =  new stella.Absyn.ListBinding(); 
				}
				break;
			case 2:
				enterOuterAlt(_localctx, 2);
				{
				setState(572);
				((ListBindingContext)_localctx).p_2_1 = binding();
				 ((ListBindingContext)_localctx).result =  new stella.Absyn.ListBinding(); _localctx.result.addLast(((ListBindingContext)_localctx).p_2_1.result); 
				}
				break;
			case 3:
				enterOuterAlt(_localctx, 3);
				{
				setState(575);
				((ListBindingContext)_localctx).p_3_1 = binding();
				setState(576);
				match(Surrogate_id_SYMB_1);
				setState(577);
				((ListBindingContext)_localctx).p_3_3 = listBinding();
				 ((ListBindingContext)_localctx).result =  ((ListBindingContext)_localctx).p_3_3.result; _localctx.result.addFirst(((ListBindingContext)_localctx).p_3_1.result); 
				}
				break;
			}
		}
		catch (RecognitionException re) {
			_localctx.exception = re;
			_errHandler.reportError(this, re);
			_errHandler.recover(this, re);
		}
		finally {
			exitRule();
		}
		return _localctx;
	}

	public static class Expr0Context extends ParserRuleContext {
		public stella.Absyn.Expr result;
		public Expr1Context p_1_1;
		public Expr1Context p_1_3;
		public Expr1Context p_2_1;
		public Expr1Context p_2_3;
		public Expr1Context p_3_1;
		public Expr1Context p_3_3;
		public Expr1Context p_4_1;
		public Expr1Context p_4_3;
		public Expr1Context p_5_1;
		public Expr1Context p_5_3;
		public Expr1Context p_6_1;
		public Expr1Context p_6_3;
		public TerminalNode Surrogate_id_SYMB_10() { return getToken(stellaParser.Surrogate_id_SYMB_10, 0); }
		public List<Expr1Context> expr1() {
			return getRuleContexts(Expr1Context.class);
		}
		public Expr1Context expr1(int i) {
			return getRuleContext(Expr1Context.class,i);
		}
		public TerminalNode Surrogate_id_SYMB_14() { return getToken(stellaParser.Surrogate_id_SYMB_14, 0); }
		public TerminalNode Surrogate_id_SYMB_11() { return getToken(stellaParser.Surrogate_id_SYMB_11, 0); }
		public TerminalNode Surrogate_id_SYMB_15() { return getToken(stellaParser.Surrogate_id_SYMB_15, 0); }
		public TerminalNode Surrogate_id_SYMB_16() { return getToken(stellaParser.Surrogate_id_SYMB_16, 0); }
		public TerminalNode Surrogate_id_SYMB_17() { return getToken(stellaParser.Surrogate_id_SYMB_17, 0); }
		public Expr0Context(ParserRuleContext parent, int invokingState) {
			super(parent, invokingState);
		}
		@Override public int getRuleIndex() { return RULE_expr0; }
		@Override
		public void enterRule(ParseTreeListener listener) {
			if ( listener instanceof stellaParserListener ) ((stellaParserListener)listener).enterExpr0(this);
		}
		@Override
		public void exitRule(ParseTreeListener listener) {
			if ( listener instanceof stellaParserListener ) ((stellaParserListener)listener).exitExpr0(this);
		}
	}

	public final Expr0Context expr0() throws RecognitionException {
		Expr0Context _localctx = new Expr0Context(_ctx, getState());
		enterRule(_localctx, 126, RULE_expr0);
		try {
			setState(612);
			_errHandler.sync(this);
			switch ( getInterpreter().adaptivePredict(_input,16,_ctx) ) {
			case 1:
				enterOuterAlt(_localctx, 1);
				{
				setState(582);
				((Expr0Context)_localctx).p_1_1 = expr1(0);
				setState(583);
				match(Surrogate_id_SYMB_10);
				setState(584);
				((Expr0Context)_localctx).p_1_3 = expr1(0);
				 ((Expr0Context)_localctx).result =  new stella.Absyn.LessThan(((Expr0Context)_localctx).p_1_1.result,((Expr0Context)_localctx).p_1_3.result); 
				}
				break;
			case 2:
				enterOuterAlt(_localctx, 2);
				{
				setState(587);
				((Expr0Context)_localctx).p_2_1 = expr1(0);
				setState(588);
				match(Surrogate_id_SYMB_14);
				setState(589);
				((Expr0Context)_localctx).p_2_3 = expr1(0);
				 ((Expr0Context)_localctx).result =  new stella.Absyn.LessThanOrEqual(((Expr0Context)_localctx).p_2_1.result,((Expr0Context)_localctx).p_2_3.result); 
				}
				break;
			case 3:
				enterOuterAlt(_localctx, 3);
				{
				setState(592);
				((Expr0Context)_localctx).p_3_1 = expr1(0);
				setState(593);
				match(Surrogate_id_SYMB_11);
				setState(594);
				((Expr0Context)_localctx).p_3_3 = expr1(0);
				 ((Expr0Context)_localctx).result =  new stella.Absyn.GreaterThan(((Expr0Context)_localctx).p_3_1.result,((Expr0Context)_localctx).p_3_3.result); 
				}
				break;
			case 4:
				enterOuterAlt(_localctx, 4);
				{
				setState(597);
				((Expr0Context)_localctx).p_4_1 = expr1(0);
				setState(598);
				match(Surrogate_id_SYMB_15);
				setState(599);
				((Expr0Context)_localctx).p_4_3 = expr1(0);
				 ((Expr0Context)_localctx).result =  new stella.Absyn.GreaterThanOrEqual(((Expr0Context)_localctx).p_4_1.result,((Expr0Context)_localctx).p_4_3.result); 
				}
				break;
			case 5:
				enterOuterAlt(_localctx, 5);
				{
				setState(602);
				((Expr0Context)_localctx).p_5_1 = expr1(0);
				setState(603);
				match(Surrogate_id_SYMB_16);
				setState(604);
				((Expr0Context)_localctx).p_5_3 = expr1(0);
				 ((Expr0Context)_localctx).result =  new stella.Absyn.Equal(((Expr0Context)_localctx).p_5_1.result,((Expr0Context)_localctx).p_5_3.result); 
				}
				break;
			case 6:
				enterOuterAlt(_localctx, 6);
				{
				setState(607);
				((Expr0Context)_localctx).p_6_1 = expr1(0);
				setState(608);
				match(Surrogate_id_SYMB_17);
				setState(609);
				((Expr0Context)_localctx).p_6_3 = expr1(0);
				 ((Expr0Context)_localctx).result =  new stella.Absyn.NotEqual(((Expr0Context)_localctx).p_6_1.result,((Expr0Context)_localctx).p_6_3.result); 
				}
				break;
			}
		}
		catch (RecognitionException re) {
			_localctx.exception = re;
			_errHandler.reportError(this, re);
			_errHandler.recover(this, re);
		}
		finally {
			exitRule();
		}
		return _localctx;
	}

	public static class Expr1Context extends ParserRuleContext {
		public stella.Absyn.Expr result;
		public Expr1Context p_1_1;
		public Expr1Context p_8_1;
		public Expr1Context p_9_1;
		public ListParamDeclContext p_2_3;
		public ExprContext p_2_7;
		public ListExprContext p_3_2;
		public ListBindingContext p_4_3;
		public Token p_5_2;
		public ExprContext p_5_4;
		public Expr1Context p_6_2;
		public ListMatchCaseContext p_6_4;
		public ListExprContext p_7_2;
		public Expr2Context p_10_1;
		public TypeContext p_1_3;
		public Expr2Context p_8_3;
		public Expr2Context p_9_3;
		public TerminalNode Surrogate_id_SYMB_38() { return getToken(stellaParser.Surrogate_id_SYMB_38, 0); }
		public TerminalNode Surrogate_id_SYMB_2() { return getToken(stellaParser.Surrogate_id_SYMB_2, 0); }
		public TerminalNode Surrogate_id_SYMB_3() { return getToken(stellaParser.Surrogate_id_SYMB_3, 0); }
		public TerminalNode Surrogate_id_SYMB_4() { return getToken(stellaParser.Surrogate_id_SYMB_4, 0); }
		public TerminalNode Surrogate_id_SYMB_49() { return getToken(stellaParser.Surrogate_id_SYMB_49, 0); }
		public TerminalNode Surrogate_id_SYMB_0() { return getToken(stellaParser.Surrogate_id_SYMB_0, 0); }
		public TerminalNode Surrogate_id_SYMB_5() { return getToken(stellaParser.Surrogate_id_SYMB_5, 0); }
		public ListParamDeclContext listParamDecl() {
			return getRuleContext(ListParamDeclContext.class,0);
		}
		public ExprContext expr() {
			return getRuleContext(ExprContext.class,0);
		}
		public ListExprContext listExpr() {
			return getRuleContext(ListExprContext.class,0);
		}
		public TerminalNode Surrogate_id_SYMB_48() { return getToken(stellaParser.Surrogate_id_SYMB_48, 0); }
		public ListBindingContext listBinding() {
			return getRuleContext(ListBindingContext.class,0);
		}
		public TerminalNode Surrogate_id_SYMB_10() { return getToken(stellaParser.Surrogate_id_SYMB_10, 0); }
		public TerminalNode Surrogate_id_SYMB_6() { return getToken(stellaParser.Surrogate_id_SYMB_6, 0); }
		public TerminalNode Surrogate_id_SYMB_11() { return getToken(stellaParser.Surrogate_id_SYMB_11, 0); }
		public TerminalNode StellaIdent() { return getToken(stellaParser.StellaIdent, 0); }
		public TerminalNode Surrogate_id_SYMB_45() { return getToken(stellaParser.Surrogate_id_SYMB_45, 0); }
		public Expr1Context expr1() {
			return getRuleContext(Expr1Context.class,0);
		}
		public ListMatchCaseContext listMatchCase() {
			return getRuleContext(ListMatchCaseContext.class,0);
		}
		public TerminalNode Surrogate_id_SYMB_12() { return getToken(stellaParser.Surrogate_id_SYMB_12, 0); }
		public TerminalNode Surrogate_id_SYMB_13() { return getToken(stellaParser.Surrogate_id_SYMB_13, 0); }
		public Expr2Context expr2() {
			return getRuleContext(Expr2Context.class,0);
		}
		public TerminalNode Surrogate_id_SYMB_31() { return getToken(stellaParser.Surrogate_id_SYMB_31, 0); }
		public TypeContext type() {
			return getRuleContext(TypeContext.class,0);
		}
		public TerminalNode Surrogate_id_SYMB_18() { return getToken(stellaParser.Surrogate_id_SYMB_18, 0); }
		public TerminalNode Surrogate_id_SYMB_47() { return getToken(stellaParser.Surrogate_id_SYMB_47, 0); }
		public Expr1Context(ParserRuleContext parent, int invokingState) {
			super(parent, invokingState);
		}
		@Override public int getRuleIndex() { return RULE_expr1; }
		@Override
		public void enterRule(ParseTreeListener listener) {
			if ( listener instanceof stellaParserListener ) ((stellaParserListener)listener).enterExpr1(this);
		}
		@Override
		public void exitRule(ParseTreeListener listener) {
			if ( listener instanceof stellaParserListener ) ((stellaParserListener)listener).exitExpr1(this);
		}
	}

	public final Expr1Context expr1() throws RecognitionException {
		return expr1(0);
	}

	private Expr1Context expr1(int _p) throws RecognitionException {
		ParserRuleContext _parentctx = _ctx;
		int _parentState = getState();
		Expr1Context _localctx = new Expr1Context(_ctx, _parentState);
		Expr1Context _prevctx = _localctx;
		int _startState = 128;
		enterRecursionRule(_localctx, 128, RULE_expr1, _p);
		try {
			int _alt;
			enterOuterAlt(_localctx, 1);
			{
			setState(659);
			_errHandler.sync(this);
			switch (_input.LA(1)) {
			case Surrogate_id_SYMB_38:
				{
				setState(615);
				match(Surrogate_id_SYMB_38);
				setState(616);
				match(Surrogate_id_SYMB_2);
				setState(617);
				((Expr1Context)_localctx).p_2_3 = listParamDecl();
				setState(618);
				match(Surrogate_id_SYMB_3);
				setState(619);
				match(Surrogate_id_SYMB_4);
				setState(620);
				match(Surrogate_id_SYMB_49);
				setState(621);
				((Expr1Context)_localctx).p_2_7 = expr();
				setState(622);
				match(Surrogate_id_SYMB_0);
				setState(623);
				match(Surrogate_id_SYMB_5);
				 ((Expr1Context)_localctx).result =  new stella.Absyn.Abstraction(((Expr1Context)_localctx).p_2_3.result,((Expr1Context)_localctx).p_2_7.result); 
				}
				break;
			case Surrogate_id_SYMB_4:
				{
				setState(626);
				match(Surrogate_id_SYMB_4);
				setState(627);
				((Expr1Context)_localctx).p_3_2 = listExpr();
				setState(628);
				match(Surrogate_id_SYMB_5);
				 ((Expr1Context)_localctx).result =  new stella.Absyn.Tuple(((Expr1Context)_localctx).p_3_2.result); 
				}
				break;
			case Surrogate_id_SYMB_48:
				{
				setState(631);
				match(Surrogate_id_SYMB_48);
				setState(632);
				match(Surrogate_id_SYMB_4);
				setState(633);
				((Expr1Context)_localctx).p_4_3 = listBinding();
				setState(634);
				match(Surrogate_id_SYMB_5);
				 ((Expr1Context)_localctx).result =  new stella.Absyn.Record(((Expr1Context)_localctx).p_4_3.result); 
				}
				break;
			case Surrogate_id_SYMB_10:
				{
				setState(637);
				match(Surrogate_id_SYMB_10);
				setState(638);
				((Expr1Context)_localctx).p_5_2 = match(StellaIdent);
				setState(639);
				match(Surrogate_id_SYMB_6);
				setState(640);
				((Expr1Context)_localctx).p_5_4 = expr();
				setState(641);
				match(Surrogate_id_SYMB_11);
				 ((Expr1Context)_localctx).result =  new stella.Absyn.Variant(((Expr1Context)_localctx).p_5_2.getText(),((Expr1Context)_localctx).p_5_4.result); 
				}
				break;
			case Surrogate_id_SYMB_45:
				{
				setState(644);
				match(Surrogate_id_SYMB_45);
				setState(645);
				((Expr1Context)_localctx).p_6_2 = expr1(0);
				setState(646);
				match(Surrogate_id_SYMB_4);
				setState(647);
				((Expr1Context)_localctx).p_6_4 = listMatchCase();
				setState(648);
				match(Surrogate_id_SYMB_5);
				 ((Expr1Context)_localctx).result =  new stella.Absyn.Match(((Expr1Context)_localctx).p_6_2.result,((Expr1Context)_localctx).p_6_4.result); 
				}
				break;
			case Surrogate_id_SYMB_12:
				{
				setState(651);
				match(Surrogate_id_SYMB_12);
				setState(652);
				((Expr1Context)_localctx).p_7_2 = listExpr();
				setState(653);
				match(Surrogate_id_SYMB_13);
				 ((Expr1Context)_localctx).result =  new stella.Absyn.List(((Expr1Context)_localctx).p_7_2.result); 
				}
				break;
			case Surrogate_id_SYMB_2:
			case Surrogate_id_SYMB_20:
			case Surrogate_id_SYMB_21:
			case Surrogate_id_SYMB_22:
			case Surrogate_id_SYMB_23:
			case Surrogate_id_SYMB_24:
			case Surrogate_id_SYMB_25:
			case Surrogate_id_SYMB_32:
			case Surrogate_id_SYMB_36:
			case Surrogate_id_SYMB_37:
			case Surrogate_id_SYMB_39:
			case Surrogate_id_SYMB_46:
			case Surrogate_id_SYMB_51:
			case Surrogate_id_SYMB_54:
			case Surrogate_id_SYMB_56:
			case StellaIdent:
			case INTEGER:
				{
				setState(656);
				((Expr1Context)_localctx).p_10_1 = expr2(0);
				 ((Expr1Context)_localctx).result =  ((Expr1Context)_localctx).p_10_1.result; 
				}
				break;
			default:
				throw new NoViableAltException(this);
			}
			_ctx.stop = _input.LT(-1);
			setState(678);
			_errHandler.sync(this);
			_alt = getInterpreter().adaptivePredict(_input,19,_ctx);
			while ( _alt!=2 && _alt!=org.antlr.v4.runtime.atn.ATN.INVALID_ALT_NUMBER ) {
				if ( _alt==1 ) {
					if ( _parseListeners!=null ) triggerExitRuleEvent();
					_prevctx = _localctx;
					{
					setState(676);
					_errHandler.sync(this);
					switch ( getInterpreter().adaptivePredict(_input,18,_ctx) ) {
					case 1:
						{
						_localctx = new Expr1Context(_parentctx, _parentState);
						_localctx.p_1_1 = _prevctx;
						_localctx.p_1_1 = _prevctx;
						pushNewRecursionContext(_localctx, _startState, RULE_expr1);
						setState(661);
						if (!(precpred(_ctx, 10))) throw new FailedPredicateException(this, "precpred(_ctx, 10)");
						setState(662);
						match(Surrogate_id_SYMB_31);
						setState(663);
						((Expr1Context)_localctx).p_1_3 = type();
						 ((Expr1Context)_localctx).result =  new stella.Absyn.TypeAsc(((Expr1Context)_localctx).p_1_1.result,((Expr1Context)_localctx).p_1_3.result); 
						}
						break;
					case 2:
						{
						_localctx = new Expr1Context(_parentctx, _parentState);
						_localctx.p_8_1 = _prevctx;
						_localctx.p_8_1 = _prevctx;
						pushNewRecursionContext(_localctx, _startState, RULE_expr1);
						setState(666);
						if (!(precpred(_ctx, 3))) throw new FailedPredicateException(this, "precpred(_ctx, 3)");
						setState(667);
						match(Surrogate_id_SYMB_18);
						setState(668);
						((Expr1Context)_localctx).p_8_3 = expr2(0);
						 ((Expr1Context)_localctx).result =  new stella.Absyn.Add(((Expr1Context)_localctx).p_8_1.result,((Expr1Context)_localctx).p_8_3.result); 
						}
						break;
					case 3:
						{
						_localctx = new Expr1Context(_parentctx, _parentState);
						_localctx.p_9_1 = _prevctx;
						_localctx.p_9_1 = _prevctx;
						pushNewRecursionContext(_localctx, _startState, RULE_expr1);
						setState(671);
						if (!(precpred(_ctx, 2))) throw new FailedPredicateException(this, "precpred(_ctx, 2)");
						setState(672);
						match(Surrogate_id_SYMB_47);
						setState(673);
						((Expr1Context)_localctx).p_9_3 = expr2(0);
						 ((Expr1Context)_localctx).result =  new stella.Absyn.LogicOr(((Expr1Context)_localctx).p_9_1.result,((Expr1Context)_localctx).p_9_3.result); 
						}
						break;
					}
					} 
				}
				setState(680);
				_errHandler.sync(this);
				_alt = getInterpreter().adaptivePredict(_input,19,_ctx);
			}
			}
		}
		catch (RecognitionException re) {
			_localctx.exception = re;
			_errHandler.reportError(this, re);
			_errHandler.recover(this, re);
		}
		finally {
			unrollRecursionContexts(_parentctx);
		}
		return _localctx;
	}

	public static class Expr2Context extends ParserRuleContext {
		public stella.Absyn.Expr result;
		public Expr2Context p_1_1;
		public Expr2Context p_2_1;
		public Expr3Context p_3_1;
		public Expr3Context p_1_3;
		public Expr3Context p_2_3;
		public Expr3Context expr3() {
			return getRuleContext(Expr3Context.class,0);
		}
		public TerminalNode Surrogate_id_SYMB_19() { return getToken(stellaParser.Surrogate_id_SYMB_19, 0); }
		public Expr2Context expr2() {
			return getRuleContext(Expr2Context.class,0);
		}
		public TerminalNode Surrogate_id_SYMB_30() { return getToken(stellaParser.Surrogate_id_SYMB_30, 0); }
		public Expr2Context(ParserRuleContext parent, int invokingState) {
			super(parent, invokingState);
		}
		@Override public int getRuleIndex() { return RULE_expr2; }
		@Override
		public void enterRule(ParseTreeListener listener) {
			if ( listener instanceof stellaParserListener ) ((stellaParserListener)listener).enterExpr2(this);
		}
		@Override
		public void exitRule(ParseTreeListener listener) {
			if ( listener instanceof stellaParserListener ) ((stellaParserListener)listener).exitExpr2(this);
		}
	}

	public final Expr2Context expr2() throws RecognitionException {
		return expr2(0);
	}

	private Expr2Context expr2(int _p) throws RecognitionException {
		ParserRuleContext _parentctx = _ctx;
		int _parentState = getState();
		Expr2Context _localctx = new Expr2Context(_ctx, _parentState);
		Expr2Context _prevctx = _localctx;
		int _startState = 130;
		enterRecursionRule(_localctx, 130, RULE_expr2, _p);
		try {
			int _alt;
			enterOuterAlt(_localctx, 1);
			{
			{
			setState(682);
			((Expr2Context)_localctx).p_3_1 = expr3(0);
			 ((Expr2Context)_localctx).result =  ((Expr2Context)_localctx).p_3_1.result; 
			}
			_ctx.stop = _input.LT(-1);
			setState(697);
			_errHandler.sync(this);
			_alt = getInterpreter().adaptivePredict(_input,21,_ctx);
			while ( _alt!=2 && _alt!=org.antlr.v4.runtime.atn.ATN.INVALID_ALT_NUMBER ) {
				if ( _alt==1 ) {
					if ( _parseListeners!=null ) triggerExitRuleEvent();
					_prevctx = _localctx;
					{
					setState(695);
					_errHandler.sync(this);
					switch ( getInterpreter().adaptivePredict(_input,20,_ctx) ) {
					case 1:
						{
						_localctx = new Expr2Context(_parentctx, _parentState);
						_localctx.p_1_1 = _prevctx;
						_localctx.p_1_1 = _prevctx;
						pushNewRecursionContext(_localctx, _startState, RULE_expr2);
						setState(685);
						if (!(precpred(_ctx, 3))) throw new FailedPredicateException(this, "precpred(_ctx, 3)");
						setState(686);
						match(Surrogate_id_SYMB_19);
						setState(687);
						((Expr2Context)_localctx).p_1_3 = expr3(0);
						 ((Expr2Context)_localctx).result =  new stella.Absyn.Multiply(((Expr2Context)_localctx).p_1_1.result,((Expr2Context)_localctx).p_1_3.result); 
						}
						break;
					case 2:
						{
						_localctx = new Expr2Context(_parentctx, _parentState);
						_localctx.p_2_1 = _prevctx;
						_localctx.p_2_1 = _prevctx;
						pushNewRecursionContext(_localctx, _startState, RULE_expr2);
						setState(690);
						if (!(precpred(_ctx, 2))) throw new FailedPredicateException(this, "precpred(_ctx, 2)");
						setState(691);
						match(Surrogate_id_SYMB_30);
						setState(692);
						((Expr2Context)_localctx).p_2_3 = expr3(0);
						 ((Expr2Context)_localctx).result =  new stella.Absyn.LogicAnd(((Expr2Context)_localctx).p_2_1.result,((Expr2Context)_localctx).p_2_3.result); 
						}
						break;
					}
					} 
				}
				setState(699);
				_errHandler.sync(this);
				_alt = getInterpreter().adaptivePredict(_input,21,_ctx);
			}
			}
		}
		catch (RecognitionException re) {
			_localctx.exception = re;
			_errHandler.reportError(this, re);
			_errHandler.recover(this, re);
		}
		finally {
			unrollRecursionContexts(_parentctx);
		}
		return _localctx;
	}

	public static class Expr3Context extends ParserRuleContext {
		public stella.Absyn.Expr result;
		public Expr3Context p_1_1;
		public Expr4Context p_2_1;
		public ListExprContext p_1_3;
		public Expr4Context expr4() {
			return getRuleContext(Expr4Context.class,0);
		}
		public TerminalNode Surrogate_id_SYMB_2() { return getToken(stellaParser.Surrogate_id_SYMB_2, 0); }
		public TerminalNode Surrogate_id_SYMB_3() { return getToken(stellaParser.Surrogate_id_SYMB_3, 0); }
		public Expr3Context expr3() {
			return getRuleContext(Expr3Context.class,0);
		}
		public ListExprContext listExpr() {
			return getRuleContext(ListExprContext.class,0);
		}
		public Expr3Context(ParserRuleContext parent, int invokingState) {
			super(parent, invokingState);
		}
		@Override public int getRuleIndex() { return RULE_expr3; }
		@Override
		public void enterRule(ParseTreeListener listener) {
			if ( listener instanceof stellaParserListener ) ((stellaParserListener)listener).enterExpr3(this);
		}
		@Override
		public void exitRule(ParseTreeListener listener) {
			if ( listener instanceof stellaParserListener ) ((stellaParserListener)listener).exitExpr3(this);
		}
	}

	public final Expr3Context expr3() throws RecognitionException {
		return expr3(0);
	}

	private Expr3Context expr3(int _p) throws RecognitionException {
		ParserRuleContext _parentctx = _ctx;
		int _parentState = getState();
		Expr3Context _localctx = new Expr3Context(_ctx, _parentState);
		Expr3Context _prevctx = _localctx;
		int _startState = 132;
		enterRecursionRule(_localctx, 132, RULE_expr3, _p);
		try {
			int _alt;
			enterOuterAlt(_localctx, 1);
			{
			{
			setState(701);
			((Expr3Context)_localctx).p_2_1 = expr4();
			 ((Expr3Context)_localctx).result =  ((Expr3Context)_localctx).p_2_1.result; 
			}
			_ctx.stop = _input.LT(-1);
			setState(712);
			_errHandler.sync(this);
			_alt = getInterpreter().adaptivePredict(_input,22,_ctx);
			while ( _alt!=2 && _alt!=org.antlr.v4.runtime.atn.ATN.INVALID_ALT_NUMBER ) {
				if ( _alt==1 ) {
					if ( _parseListeners!=null ) triggerExitRuleEvent();
					_prevctx = _localctx;
					{
					{
					_localctx = new Expr3Context(_parentctx, _parentState);
					_localctx.p_1_1 = _prevctx;
					_localctx.p_1_1 = _prevctx;
					pushNewRecursionContext(_localctx, _startState, RULE_expr3);
					setState(704);
					if (!(precpred(_ctx, 2))) throw new FailedPredicateException(this, "precpred(_ctx, 2)");
					setState(705);
					match(Surrogate_id_SYMB_2);
					setState(706);
					((Expr3Context)_localctx).p_1_3 = listExpr();
					setState(707);
					match(Surrogate_id_SYMB_3);
					 ((Expr3Context)_localctx).result =  new stella.Absyn.Application(((Expr3Context)_localctx).p_1_1.result,((Expr3Context)_localctx).p_1_3.result); 
					}
					} 
				}
				setState(714);
				_errHandler.sync(this);
				_alt = getInterpreter().adaptivePredict(_input,22,_ctx);
			}
			}
		}
		catch (RecognitionException re) {
			_localctx.exception = re;
			_errHandler.reportError(this, re);
			_errHandler.recover(this, re);
		}
		finally {
			unrollRecursionContexts(_parentctx);
		}
		return _localctx;
	}

	public static class Expr4Context extends ParserRuleContext {
		public stella.Absyn.Expr result;
		public ExprContext p_1_3;
		public ExprContext p_1_5;
		public ExprContext p_2_3;
		public ExprContext p_3_3;
		public ExprContext p_4_3;
		public ExprContext p_5_3;
		public ExprContext p_6_3;
		public ExprContext p_7_3;
		public ExprContext p_8_3;
		public ExprContext p_9_3;
		public ExprContext p_10_3;
		public ExprContext p_10_5;
		public ExprContext p_10_7;
		public TypeContext p_11_3;
		public Expr5Context p_11_5;
		public TypeContext p_12_3;
		public Expr5Context p_12_5;
		public Expr5Context p_13_1;
		public TerminalNode Surrogate_id_SYMB_32() { return getToken(stellaParser.Surrogate_id_SYMB_32, 0); }
		public TerminalNode Surrogate_id_SYMB_2() { return getToken(stellaParser.Surrogate_id_SYMB_2, 0); }
		public List<TerminalNode> Surrogate_id_SYMB_1() { return getTokens(stellaParser.Surrogate_id_SYMB_1); }
		public TerminalNode Surrogate_id_SYMB_1(int i) {
			return getToken(stellaParser.Surrogate_id_SYMB_1, i);
		}
		public TerminalNode Surrogate_id_SYMB_3() { return getToken(stellaParser.Surrogate_id_SYMB_3, 0); }
		public List<ExprContext> expr() {
			return getRuleContexts(ExprContext.class);
		}
		public ExprContext expr(int i) {
			return getRuleContext(ExprContext.class,i);
		}
		public TerminalNode Surrogate_id_SYMB_20() { return getToken(stellaParser.Surrogate_id_SYMB_20, 0); }
		public TerminalNode Surrogate_id_SYMB_21() { return getToken(stellaParser.Surrogate_id_SYMB_21, 0); }
		public TerminalNode Surrogate_id_SYMB_22() { return getToken(stellaParser.Surrogate_id_SYMB_22, 0); }
		public TerminalNode Surrogate_id_SYMB_51() { return getToken(stellaParser.Surrogate_id_SYMB_51, 0); }
		public TerminalNode Surrogate_id_SYMB_46() { return getToken(stellaParser.Surrogate_id_SYMB_46, 0); }
		public TerminalNode Surrogate_id_SYMB_23() { return getToken(stellaParser.Surrogate_id_SYMB_23, 0); }
		public TerminalNode Surrogate_id_SYMB_24() { return getToken(stellaParser.Surrogate_id_SYMB_24, 0); }
		public TerminalNode Surrogate_id_SYMB_37() { return getToken(stellaParser.Surrogate_id_SYMB_37, 0); }
		public TerminalNode Surrogate_id_SYMB_25() { return getToken(stellaParser.Surrogate_id_SYMB_25, 0); }
		public TerminalNode Surrogate_id_SYMB_39() { return getToken(stellaParser.Surrogate_id_SYMB_39, 0); }
		public TerminalNode Surrogate_id_SYMB_12() { return getToken(stellaParser.Surrogate_id_SYMB_12, 0); }
		public TerminalNode Surrogate_id_SYMB_13() { return getToken(stellaParser.Surrogate_id_SYMB_13, 0); }
		public TypeContext type() {
			return getRuleContext(TypeContext.class,0);
		}
		public Expr5Context expr5() {
			return getRuleContext(Expr5Context.class,0);
		}
		public TerminalNode Surrogate_id_SYMB_56() { return getToken(stellaParser.Surrogate_id_SYMB_56, 0); }
		public Expr4Context(ParserRuleContext parent, int invokingState) {
			super(parent, invokingState);
		}
		@Override public int getRuleIndex() { return RULE_expr4; }
		@Override
		public void enterRule(ParseTreeListener listener) {
			if ( listener instanceof stellaParserListener ) ((stellaParserListener)listener).enterExpr4(this);
		}
		@Override
		public void exitRule(ParseTreeListener listener) {
			if ( listener instanceof stellaParserListener ) ((stellaParserListener)listener).exitExpr4(this);
		}
	}

	public final Expr4Context expr4() throws RecognitionException {
		Expr4Context _localctx = new Expr4Context(_ctx, getState());
		enterRule(_localctx, 134, RULE_expr4);
		try {
			setState(798);
			_errHandler.sync(this);
			switch (_input.LA(1)) {
			case Surrogate_id_SYMB_32:
				enterOuterAlt(_localctx, 1);
				{
				setState(715);
				match(Surrogate_id_SYMB_32);
				setState(716);
				match(Surrogate_id_SYMB_2);
				setState(717);
				((Expr4Context)_localctx).p_1_3 = expr();
				setState(718);
				match(Surrogate_id_SYMB_1);
				setState(719);
				((Expr4Context)_localctx).p_1_5 = expr();
				setState(720);
				match(Surrogate_id_SYMB_3);
				 ((Expr4Context)_localctx).result =  new stella.Absyn.ConsList(((Expr4Context)_localctx).p_1_3.result,((Expr4Context)_localctx).p_1_5.result); 
				}
				break;
			case Surrogate_id_SYMB_20:
				enterOuterAlt(_localctx, 2);
				{
				setState(723);
				match(Surrogate_id_SYMB_20);
				setState(724);
				match(Surrogate_id_SYMB_2);
				setState(725);
				((Expr4Context)_localctx).p_2_3 = expr();
				setState(726);
				match(Surrogate_id_SYMB_3);
				 ((Expr4Context)_localctx).result =  new stella.Absyn.Head(((Expr4Context)_localctx).p_2_3.result); 
				}
				break;
			case Surrogate_id_SYMB_21:
				enterOuterAlt(_localctx, 3);
				{
				setState(729);
				match(Surrogate_id_SYMB_21);
				setState(730);
				match(Surrogate_id_SYMB_2);
				setState(731);
				((Expr4Context)_localctx).p_3_3 = expr();
				setState(732);
				match(Surrogate_id_SYMB_3);
				 ((Expr4Context)_localctx).result =  new stella.Absyn.IsEmpty(((Expr4Context)_localctx).p_3_3.result); 
				}
				break;
			case Surrogate_id_SYMB_22:
				enterOuterAlt(_localctx, 4);
				{
				setState(735);
				match(Surrogate_id_SYMB_22);
				setState(736);
				match(Surrogate_id_SYMB_2);
				setState(737);
				((Expr4Context)_localctx).p_4_3 = expr();
				setState(738);
				match(Surrogate_id_SYMB_3);
				 ((Expr4Context)_localctx).result =  new stella.Absyn.Tail(((Expr4Context)_localctx).p_4_3.result); 
				}
				break;
			case Surrogate_id_SYMB_51:
				enterOuterAlt(_localctx, 5);
				{
				setState(741);
				match(Surrogate_id_SYMB_51);
				setState(742);
				match(Surrogate_id_SYMB_2);
				setState(743);
				((Expr4Context)_localctx).p_5_3 = expr();
				setState(744);
				match(Surrogate_id_SYMB_3);
				 ((Expr4Context)_localctx).result =  new stella.Absyn.Succ(((Expr4Context)_localctx).p_5_3.result); 
				}
				break;
			case Surrogate_id_SYMB_46:
				enterOuterAlt(_localctx, 6);
				{
				setState(747);
				match(Surrogate_id_SYMB_46);
				setState(748);
				match(Surrogate_id_SYMB_2);
				setState(749);
				((Expr4Context)_localctx).p_6_3 = expr();
				setState(750);
				match(Surrogate_id_SYMB_3);
				 ((Expr4Context)_localctx).result =  new stella.Absyn.LogicNot(((Expr4Context)_localctx).p_6_3.result); 
				}
				break;
			case Surrogate_id_SYMB_23:
				enterOuterAlt(_localctx, 7);
				{
				setState(753);
				match(Surrogate_id_SYMB_23);
				setState(754);
				match(Surrogate_id_SYMB_2);
				setState(755);
				((Expr4Context)_localctx).p_7_3 = expr();
				setState(756);
				match(Surrogate_id_SYMB_3);
				 ((Expr4Context)_localctx).result =  new stella.Absyn.Pred(((Expr4Context)_localctx).p_7_3.result); 
				}
				break;
			case Surrogate_id_SYMB_24:
				enterOuterAlt(_localctx, 8);
				{
				setState(759);
				match(Surrogate_id_SYMB_24);
				setState(760);
				match(Surrogate_id_SYMB_2);
				setState(761);
				((Expr4Context)_localctx).p_8_3 = expr();
				setState(762);
				match(Surrogate_id_SYMB_3);
				 ((Expr4Context)_localctx).result =  new stella.Absyn.IsZero(((Expr4Context)_localctx).p_8_3.result); 
				}
				break;
			case Surrogate_id_SYMB_37:
				enterOuterAlt(_localctx, 9);
				{
				setState(765);
				match(Surrogate_id_SYMB_37);
				setState(766);
				match(Surrogate_id_SYMB_2);
				setState(767);
				((Expr4Context)_localctx).p_9_3 = expr();
				setState(768);
				match(Surrogate_id_SYMB_3);
				 ((Expr4Context)_localctx).result =  new stella.Absyn.Fix(((Expr4Context)_localctx).p_9_3.result); 
				}
				break;
			case Surrogate_id_SYMB_25:
				enterOuterAlt(_localctx, 10);
				{
				setState(771);
				match(Surrogate_id_SYMB_25);
				setState(772);
				match(Surrogate_id_SYMB_2);
				setState(773);
				((Expr4Context)_localctx).p_10_3 = expr();
				setState(774);
				match(Surrogate_id_SYMB_1);
				setState(775);
				((Expr4Context)_localctx).p_10_5 = expr();
				setState(776);
				match(Surrogate_id_SYMB_1);
				setState(777);
				((Expr4Context)_localctx).p_10_7 = expr();
				setState(778);
				match(Surrogate_id_SYMB_3);
				 ((Expr4Context)_localctx).result =  new stella.Absyn.NatRec(((Expr4Context)_localctx).p_10_3.result,((Expr4Context)_localctx).p_10_5.result,((Expr4Context)_localctx).p_10_7.result); 
				}
				break;
			case Surrogate_id_SYMB_39:
				enterOuterAlt(_localctx, 11);
				{
				setState(781);
				match(Surrogate_id_SYMB_39);
				setState(782);
				match(Surrogate_id_SYMB_12);
				setState(783);
				((Expr4Context)_localctx).p_11_3 = type();
				setState(784);
				match(Surrogate_id_SYMB_13);
				setState(785);
				((Expr4Context)_localctx).p_11_5 = expr5(0);
				 ((Expr4Context)_localctx).result =  new stella.Absyn.Fold(((Expr4Context)_localctx).p_11_3.result,((Expr4Context)_localctx).p_11_5.result); 
				}
				break;
			case Surrogate_id_SYMB_56:
				enterOuterAlt(_localctx, 12);
				{
				setState(788);
				match(Surrogate_id_SYMB_56);
				setState(789);
				match(Surrogate_id_SYMB_12);
				setState(790);
				((Expr4Context)_localctx).p_12_3 = type();
				setState(791);
				match(Surrogate_id_SYMB_13);
				setState(792);
				((Expr4Context)_localctx).p_12_5 = expr5(0);
				 ((Expr4Context)_localctx).result =  new stella.Absyn.Unfold(((Expr4Context)_localctx).p_12_3.result,((Expr4Context)_localctx).p_12_5.result); 
				}
				break;
			case Surrogate_id_SYMB_2:
			case Surrogate_id_SYMB_36:
			case Surrogate_id_SYMB_54:
			case StellaIdent:
			case INTEGER:
				enterOuterAlt(_localctx, 13);
				{
				setState(795);
				((Expr4Context)_localctx).p_13_1 = expr5(0);
				 ((Expr4Context)_localctx).result =  ((Expr4Context)_localctx).p_13_1.result; 
				}
				break;
			default:
				throw new NoViableAltException(this);
			}
		}
		catch (RecognitionException re) {
			_localctx.exception = re;
			_errHandler.reportError(this, re);
			_errHandler.recover(this, re);
		}
		finally {
			exitRule();
		}
		return _localctx;
	}

	public static class Expr5Context extends ParserRuleContext {
		public stella.Absyn.Expr result;
		public Expr5Context p_1_1;
		public Expr5Context p_2_1;
		public Token p_5_1;
		public Token p_6_1;
		public ExprContext p_7_2;
		public Token p_1_3;
		public Token p_2_3;
		public TerminalNode Surrogate_id_SYMB_54() { return getToken(stellaParser.Surrogate_id_SYMB_54, 0); }
		public TerminalNode Surrogate_id_SYMB_36() { return getToken(stellaParser.Surrogate_id_SYMB_36, 0); }
		public TerminalNode INTEGER() { return getToken(stellaParser.INTEGER, 0); }
		public TerminalNode StellaIdent() { return getToken(stellaParser.StellaIdent, 0); }
		public TerminalNode Surrogate_id_SYMB_2() { return getToken(stellaParser.Surrogate_id_SYMB_2, 0); }
		public TerminalNode Surrogate_id_SYMB_3() { return getToken(stellaParser.Surrogate_id_SYMB_3, 0); }
		public ExprContext expr() {
			return getRuleContext(ExprContext.class,0);
		}
		public TerminalNode Surrogate_id_SYMB_26() { return getToken(stellaParser.Surrogate_id_SYMB_26, 0); }
		public Expr5Context expr5() {
			return getRuleContext(Expr5Context.class,0);
		}
		public Expr5Context(ParserRuleContext parent, int invokingState) {
			super(parent, invokingState);
		}
		@Override public int getRuleIndex() { return RULE_expr5; }
		@Override
		public void enterRule(ParseTreeListener listener) {
			if ( listener instanceof stellaParserListener ) ((stellaParserListener)listener).enterExpr5(this);
		}
		@Override
		public void exitRule(ParseTreeListener listener) {
			if ( listener instanceof stellaParserListener ) ((stellaParserListener)listener).exitExpr5(this);
		}
	}

	public final Expr5Context expr5() throws RecognitionException {
		return expr5(0);
	}

	private Expr5Context expr5(int _p) throws RecognitionException {
		ParserRuleContext _parentctx = _ctx;
		int _parentState = getState();
		Expr5Context _localctx = new Expr5Context(_ctx, _parentState);
		Expr5Context _prevctx = _localctx;
		int _startState = 136;
		enterRecursionRule(_localctx, 136, RULE_expr5, _p);
		try {
			int _alt;
			enterOuterAlt(_localctx, 1);
			{
			setState(814);
			_errHandler.sync(this);
			switch (_input.LA(1)) {
			case Surrogate_id_SYMB_54:
				{
				setState(801);
				match(Surrogate_id_SYMB_54);
				 ((Expr5Context)_localctx).result =  new stella.Absyn.ConstTrue(); 
				}
				break;
			case Surrogate_id_SYMB_36:
				{
				setState(803);
				match(Surrogate_id_SYMB_36);
				 ((Expr5Context)_localctx).result =  new stella.Absyn.ConstFalse(); 
				}
				break;
			case INTEGER:
				{
				setState(805);
				((Expr5Context)_localctx).p_5_1 = match(INTEGER);
				 ((Expr5Context)_localctx).result =  new stella.Absyn.ConstInt(Integer.parseInt(((Expr5Context)_localctx).p_5_1.getText())); 
				}
				break;
			case StellaIdent:
				{
				setState(807);
				((Expr5Context)_localctx).p_6_1 = match(StellaIdent);
				 ((Expr5Context)_localctx).result =  new stella.Absyn.Var(((Expr5Context)_localctx).p_6_1.getText()); 
				}
				break;
			case Surrogate_id_SYMB_2:
				{
				setState(809);
				match(Surrogate_id_SYMB_2);
				setState(810);
				((Expr5Context)_localctx).p_7_2 = expr();
				setState(811);
				match(Surrogate_id_SYMB_3);
				 ((Expr5Context)_localctx).result =  ((Expr5Context)_localctx).p_7_2.result; 
				}
				break;
			default:
				throw new NoViableAltException(this);
			}
			_ctx.stop = _input.LT(-1);
			setState(826);
			_errHandler.sync(this);
			_alt = getInterpreter().adaptivePredict(_input,26,_ctx);
			while ( _alt!=2 && _alt!=org.antlr.v4.runtime.atn.ATN.INVALID_ALT_NUMBER ) {
				if ( _alt==1 ) {
					if ( _parseListeners!=null ) triggerExitRuleEvent();
					_prevctx = _localctx;
					{
					setState(824);
					_errHandler.sync(this);
					switch ( getInterpreter().adaptivePredict(_input,25,_ctx) ) {
					case 1:
						{
						_localctx = new Expr5Context(_parentctx, _parentState);
						_localctx.p_1_1 = _prevctx;
						_localctx.p_1_1 = _prevctx;
						pushNewRecursionContext(_localctx, _startState, RULE_expr5);
						setState(816);
						if (!(precpred(_ctx, 7))) throw new FailedPredicateException(this, "precpred(_ctx, 7)");
						setState(817);
						match(Surrogate_id_SYMB_26);
						setState(818);
						((Expr5Context)_localctx).p_1_3 = match(StellaIdent);
						 ((Expr5Context)_localctx).result =  new stella.Absyn.DotRecord(((Expr5Context)_localctx).p_1_1.result,((Expr5Context)_localctx).p_1_3.getText()); 
						}
						break;
					case 2:
						{
						_localctx = new Expr5Context(_parentctx, _parentState);
						_localctx.p_2_1 = _prevctx;
						_localctx.p_2_1 = _prevctx;
						pushNewRecursionContext(_localctx, _startState, RULE_expr5);
						setState(820);
						if (!(precpred(_ctx, 6))) throw new FailedPredicateException(this, "precpred(_ctx, 6)");
						setState(821);
						match(Surrogate_id_SYMB_26);
						setState(822);
						((Expr5Context)_localctx).p_2_3 = match(INTEGER);
						 ((Expr5Context)_localctx).result =  new stella.Absyn.DotTuple(((Expr5Context)_localctx).p_2_1.result,Integer.parseInt(((Expr5Context)_localctx).p_2_3.getText())); 
						}
						break;
					}
					} 
				}
				setState(828);
				_errHandler.sync(this);
				_alt = getInterpreter().adaptivePredict(_input,26,_ctx);
			}
			}
		}
		catch (RecognitionException re) {
			_localctx.exception = re;
			_errHandler.reportError(this, re);
			_errHandler.recover(this, re);
		}
		finally {
			unrollRecursionContexts(_parentctx);
		}
		return _localctx;
	}

	public static class TypeContext extends ParserRuleContext {
		public stella.Absyn.Type result;
		public ListTypeContext p_1_3;
		public TypeContext p_1_6;
		public Token p_2_2;
		public TypeContext p_2_4;
		public Type1Context p_3_1;
		public TerminalNode Surrogate_id_SYMB_38() { return getToken(stellaParser.Surrogate_id_SYMB_38, 0); }
		public TerminalNode Surrogate_id_SYMB_2() { return getToken(stellaParser.Surrogate_id_SYMB_2, 0); }
		public TerminalNode Surrogate_id_SYMB_3() { return getToken(stellaParser.Surrogate_id_SYMB_3, 0); }
		public TerminalNode Surrogate_id_SYMB_8() { return getToken(stellaParser.Surrogate_id_SYMB_8, 0); }
		public ListTypeContext listType() {
			return getRuleContext(ListTypeContext.class,0);
		}
		public TypeContext type() {
			return getRuleContext(TypeContext.class,0);
		}
		public TerminalNode Surrogate_id_SYMB_59() { return getToken(stellaParser.Surrogate_id_SYMB_59, 0); }
		public TerminalNode Surrogate_id_SYMB_26() { return getToken(stellaParser.Surrogate_id_SYMB_26, 0); }
		public TerminalNode StellaIdent() { return getToken(stellaParser.StellaIdent, 0); }
		public Type1Context type1() {
			return getRuleContext(Type1Context.class,0);
		}
		public TypeContext(ParserRuleContext parent, int invokingState) {
			super(parent, invokingState);
		}
		@Override public int getRuleIndex() { return RULE_type; }
		@Override
		public void enterRule(ParseTreeListener listener) {
			if ( listener instanceof stellaParserListener ) ((stellaParserListener)listener).enterType(this);
		}
		@Override
		public void exitRule(ParseTreeListener listener) {
			if ( listener instanceof stellaParserListener ) ((stellaParserListener)listener).exitType(this);
		}
	}

	public final TypeContext type() throws RecognitionException {
		TypeContext _localctx = new TypeContext(_ctx, getState());
		enterRule(_localctx, 138, RULE_type);
		try {
			setState(846);
			_errHandler.sync(this);
			switch (_input.LA(1)) {
			case Surrogate_id_SYMB_38:
				enterOuterAlt(_localctx, 1);
				{
				setState(829);
				match(Surrogate_id_SYMB_38);
				setState(830);
				match(Surrogate_id_SYMB_2);
				setState(831);
				((TypeContext)_localctx).p_1_3 = listType();
				setState(832);
				match(Surrogate_id_SYMB_3);
				setState(833);
				match(Surrogate_id_SYMB_8);
				setState(834);
				((TypeContext)_localctx).p_1_6 = type();
				 ((TypeContext)_localctx).result =  new stella.Absyn.TypeFun(((TypeContext)_localctx).p_1_3.result,((TypeContext)_localctx).p_1_6.result); 
				}
				break;
			case Surrogate_id_SYMB_59:
				enterOuterAlt(_localctx, 2);
				{
				setState(837);
				match(Surrogate_id_SYMB_59);
				setState(838);
				((TypeContext)_localctx).p_2_2 = match(StellaIdent);
				setState(839);
				match(Surrogate_id_SYMB_26);
				setState(840);
				((TypeContext)_localctx).p_2_4 = type();
				 ((TypeContext)_localctx).result =  new stella.Absyn.TypeRec(((TypeContext)_localctx).p_2_2.getText(),((TypeContext)_localctx).p_2_4.result); 
				}
				break;
			case Surrogate_id_SYMB_2:
			case Surrogate_id_SYMB_4:
			case Surrogate_id_SYMB_12:
			case Surrogate_id_SYMB_27:
			case Surrogate_id_SYMB_28:
			case Surrogate_id_SYMB_29:
			case Surrogate_id_SYMB_50:
			case Surrogate_id_SYMB_57:
			case StellaIdent:
				enterOuterAlt(_localctx, 3);
				{
				setState(843);
				((TypeContext)_localctx).p_3_1 = type1();
				 ((TypeContext)_localctx).result =  ((TypeContext)_localctx).p_3_1.result; 
				}
				break;
			default:
				throw new NoViableAltException(this);
			}
		}
		catch (RecognitionException re) {
			_localctx.exception = re;
			_errHandler.reportError(this, re);
			_errHandler.recover(this, re);
		}
		finally {
			exitRule();
		}
		return _localctx;
	}

	public static class Type1Context extends ParserRuleContext {
		public stella.Absyn.Type result;
		public ListTypeContext p_1_2;
		public ListFieldTypeContext p_2_3;
		public ListFieldTypeContext p_3_3;
		public TypeContext p_4_2;
		public Type2Context p_5_1;
		public TerminalNode Surrogate_id_SYMB_4() { return getToken(stellaParser.Surrogate_id_SYMB_4, 0); }
		public TerminalNode Surrogate_id_SYMB_5() { return getToken(stellaParser.Surrogate_id_SYMB_5, 0); }
		public ListTypeContext listType() {
			return getRuleContext(ListTypeContext.class,0);
		}
		public TerminalNode Surrogate_id_SYMB_50() { return getToken(stellaParser.Surrogate_id_SYMB_50, 0); }
		public ListFieldTypeContext listFieldType() {
			return getRuleContext(ListFieldTypeContext.class,0);
		}
		public TerminalNode Surrogate_id_SYMB_57() { return getToken(stellaParser.Surrogate_id_SYMB_57, 0); }
		public TerminalNode Surrogate_id_SYMB_10() { return getToken(stellaParser.Surrogate_id_SYMB_10, 0); }
		public TerminalNode Surrogate_id_SYMB_11() { return getToken(stellaParser.Surrogate_id_SYMB_11, 0); }
		public TerminalNode Surrogate_id_SYMB_12() { return getToken(stellaParser.Surrogate_id_SYMB_12, 0); }
		public TerminalNode Surrogate_id_SYMB_13() { return getToken(stellaParser.Surrogate_id_SYMB_13, 0); }
		public TypeContext type() {
			return getRuleContext(TypeContext.class,0);
		}
		public Type2Context type2() {
			return getRuleContext(Type2Context.class,0);
		}
		public Type1Context(ParserRuleContext parent, int invokingState) {
			super(parent, invokingState);
		}
		@Override public int getRuleIndex() { return RULE_type1; }
		@Override
		public void enterRule(ParseTreeListener listener) {
			if ( listener instanceof stellaParserListener ) ((stellaParserListener)listener).enterType1(this);
		}
		@Override
		public void exitRule(ParseTreeListener listener) {
			if ( listener instanceof stellaParserListener ) ((stellaParserListener)listener).exitType1(this);
		}
	}

	public final Type1Context type1() throws RecognitionException {
		Type1Context _localctx = new Type1Context(_ctx, getState());
		enterRule(_localctx, 140, RULE_type1);
		try {
			setState(873);
			_errHandler.sync(this);
			switch (_input.LA(1)) {
			case Surrogate_id_SYMB_4:
				enterOuterAlt(_localctx, 1);
				{
				setState(848);
				match(Surrogate_id_SYMB_4);
				setState(849);
				((Type1Context)_localctx).p_1_2 = listType();
				setState(850);
				match(Surrogate_id_SYMB_5);
				 ((Type1Context)_localctx).result =  new stella.Absyn.TypeTuple(((Type1Context)_localctx).p_1_2.result); 
				}
				break;
			case Surrogate_id_SYMB_50:
				enterOuterAlt(_localctx, 2);
				{
				setState(853);
				match(Surrogate_id_SYMB_50);
				setState(854);
				match(Surrogate_id_SYMB_4);
				setState(855);
				((Type1Context)_localctx).p_2_3 = listFieldType();
				setState(856);
				match(Surrogate_id_SYMB_5);
				 ((Type1Context)_localctx).result =  new stella.Absyn.TypeRecord(((Type1Context)_localctx).p_2_3.result); 
				}
				break;
			case Surrogate_id_SYMB_57:
				enterOuterAlt(_localctx, 3);
				{
				setState(859);
				match(Surrogate_id_SYMB_57);
				setState(860);
				match(Surrogate_id_SYMB_10);
				setState(861);
				((Type1Context)_localctx).p_3_3 = listFieldType();
				setState(862);
				match(Surrogate_id_SYMB_11);
				 ((Type1Context)_localctx).result =  new stella.Absyn.TypeVariant(((Type1Context)_localctx).p_3_3.result); 
				}
				break;
			case Surrogate_id_SYMB_12:
				enterOuterAlt(_localctx, 4);
				{
				setState(865);
				match(Surrogate_id_SYMB_12);
				setState(866);
				((Type1Context)_localctx).p_4_2 = type();
				setState(867);
				match(Surrogate_id_SYMB_13);
				 ((Type1Context)_localctx).result =  new stella.Absyn.TypeList(((Type1Context)_localctx).p_4_2.result); 
				}
				break;
			case Surrogate_id_SYMB_2:
			case Surrogate_id_SYMB_27:
			case Surrogate_id_SYMB_28:
			case Surrogate_id_SYMB_29:
			case StellaIdent:
				enterOuterAlt(_localctx, 5);
				{
				setState(870);
				((Type1Context)_localctx).p_5_1 = type2();
				 ((Type1Context)_localctx).result =  ((Type1Context)_localctx).p_5_1.result; 
				}
				break;
			default:
				throw new NoViableAltException(this);
			}
		}
		catch (RecognitionException re) {
			_localctx.exception = re;
			_errHandler.reportError(this, re);
			_errHandler.recover(this, re);
		}
		finally {
			exitRule();
		}
		return _localctx;
	}

	public static class Type2Context extends ParserRuleContext {
		public stella.Absyn.Type result;
		public Token p_4_1;
		public TypeContext p_5_2;
		public TerminalNode Surrogate_id_SYMB_27() { return getToken(stellaParser.Surrogate_id_SYMB_27, 0); }
		public TerminalNode Surrogate_id_SYMB_28() { return getToken(stellaParser.Surrogate_id_SYMB_28, 0); }
		public TerminalNode Surrogate_id_SYMB_29() { return getToken(stellaParser.Surrogate_id_SYMB_29, 0); }
		public TerminalNode StellaIdent() { return getToken(stellaParser.StellaIdent, 0); }
		public TerminalNode Surrogate_id_SYMB_2() { return getToken(stellaParser.Surrogate_id_SYMB_2, 0); }
		public TerminalNode Surrogate_id_SYMB_3() { return getToken(stellaParser.Surrogate_id_SYMB_3, 0); }
		public TypeContext type() {
			return getRuleContext(TypeContext.class,0);
		}
		public Type2Context(ParserRuleContext parent, int invokingState) {
			super(parent, invokingState);
		}
		@Override public int getRuleIndex() { return RULE_type2; }
		@Override
		public void enterRule(ParseTreeListener listener) {
			if ( listener instanceof stellaParserListener ) ((stellaParserListener)listener).enterType2(this);
		}
		@Override
		public void exitRule(ParseTreeListener listener) {
			if ( listener instanceof stellaParserListener ) ((stellaParserListener)listener).exitType2(this);
		}
	}

	public final Type2Context type2() throws RecognitionException {
		Type2Context _localctx = new Type2Context(_ctx, getState());
		enterRule(_localctx, 142, RULE_type2);
		try {
			setState(888);
			_errHandler.sync(this);
			switch (_input.LA(1)) {
			case Surrogate_id_SYMB_27:
				enterOuterAlt(_localctx, 1);
				{
				setState(875);
				match(Surrogate_id_SYMB_27);
				 ((Type2Context)_localctx).result =  new stella.Absyn.TypeBool(); 
				}
				break;
			case Surrogate_id_SYMB_28:
				enterOuterAlt(_localctx, 2);
				{
				setState(877);
				match(Surrogate_id_SYMB_28);
				 ((Type2Context)_localctx).result =  new stella.Absyn.TypeNat(); 
				}
				break;
			case Surrogate_id_SYMB_29:
				enterOuterAlt(_localctx, 3);
				{
				setState(879);
				match(Surrogate_id_SYMB_29);
				 ((Type2Context)_localctx).result =  new stella.Absyn.TypeUnit(); 
				}
				break;
			case StellaIdent:
				enterOuterAlt(_localctx, 4);
				{
				setState(881);
				((Type2Context)_localctx).p_4_1 = match(StellaIdent);
				 ((Type2Context)_localctx).result =  new stella.Absyn.TypeVar(((Type2Context)_localctx).p_4_1.getText()); 
				}
				break;
			case Surrogate_id_SYMB_2:
				enterOuterAlt(_localctx, 5);
				{
				setState(883);
				match(Surrogate_id_SYMB_2);
				setState(884);
				((Type2Context)_localctx).p_5_2 = type();
				setState(885);
				match(Surrogate_id_SYMB_3);
				 ((Type2Context)_localctx).result =  ((Type2Context)_localctx).p_5_2.result; 
				}
				break;
			default:
				throw new NoViableAltException(this);
			}
		}
		catch (RecognitionException re) {
			_localctx.exception = re;
			_errHandler.reportError(this, re);
			_errHandler.recover(this, re);
		}
		finally {
			exitRule();
		}
		return _localctx;
	}

	public static class ListTypeContext extends ParserRuleContext {
		public stella.Absyn.ListType result;
		public TypeContext p_2_1;
		public TypeContext p_3_1;
		public ListTypeContext p_3_3;
		public TypeContext type() {
			return getRuleContext(TypeContext.class,0);
		}
		public TerminalNode Surrogate_id_SYMB_1() { return getToken(stellaParser.Surrogate_id_SYMB_1, 0); }
		public ListTypeContext listType() {
			return getRuleContext(ListTypeContext.class,0);
		}
		public ListTypeContext(ParserRuleContext parent, int invokingState) {
			super(parent, invokingState);
		}
		@Override public int getRuleIndex() { return RULE_listType; }
		@Override
		public void enterRule(ParseTreeListener listener) {
			if ( listener instanceof stellaParserListener ) ((stellaParserListener)listener).enterListType(this);
		}
		@Override
		public void exitRule(ParseTreeListener listener) {
			if ( listener instanceof stellaParserListener ) ((stellaParserListener)listener).exitListType(this);
		}
	}

	public final ListTypeContext listType() throws RecognitionException {
		ListTypeContext _localctx = new ListTypeContext(_ctx, getState());
		enterRule(_localctx, 144, RULE_listType);
		try {
			setState(899);
			_errHandler.sync(this);
			switch ( getInterpreter().adaptivePredict(_input,30,_ctx) ) {
			case 1:
				enterOuterAlt(_localctx, 1);
				{
				 ((ListTypeContext)_localctx).result =  new stella.Absyn.ListType(); 
				}
				break;
			case 2:
				enterOuterAlt(_localctx, 2);
				{
				setState(891);
				((ListTypeContext)_localctx).p_2_1 = type();
				 ((ListTypeContext)_localctx).result =  new stella.Absyn.ListType(); _localctx.result.addLast(((ListTypeContext)_localctx).p_2_1.result); 
				}
				break;
			case 3:
				enterOuterAlt(_localctx, 3);
				{
				setState(894);
				((ListTypeContext)_localctx).p_3_1 = type();
				setState(895);
				match(Surrogate_id_SYMB_1);
				setState(896);
				((ListTypeContext)_localctx).p_3_3 = listType();
				 ((ListTypeContext)_localctx).result =  ((ListTypeContext)_localctx).p_3_3.result; _localctx.result.addFirst(((ListTypeContext)_localctx).p_3_1.result); 
				}
				break;
			}
		}
		catch (RecognitionException re) {
			_localctx.exception = re;
			_errHandler.reportError(this, re);
			_errHandler.recover(this, re);
		}
		finally {
			exitRule();
		}
		return _localctx;
	}

	public static class FieldTypeContext extends ParserRuleContext {
		public stella.Absyn.FieldType result;
		public Token p_1_1;
		public TypeContext p_1_3;
		public TerminalNode Surrogate_id_SYMB_7() { return getToken(stellaParser.Surrogate_id_SYMB_7, 0); }
		public TerminalNode StellaIdent() { return getToken(stellaParser.StellaIdent, 0); }
		public TypeContext type() {
			return getRuleContext(TypeContext.class,0);
		}
		public FieldTypeContext(ParserRuleContext parent, int invokingState) {
			super(parent, invokingState);
		}
		@Override public int getRuleIndex() { return RULE_fieldType; }
		@Override
		public void enterRule(ParseTreeListener listener) {
			if ( listener instanceof stellaParserListener ) ((stellaParserListener)listener).enterFieldType(this);
		}
		@Override
		public void exitRule(ParseTreeListener listener) {
			if ( listener instanceof stellaParserListener ) ((stellaParserListener)listener).exitFieldType(this);
		}
	}

	public final FieldTypeContext fieldType() throws RecognitionException {
		FieldTypeContext _localctx = new FieldTypeContext(_ctx, getState());
		enterRule(_localctx, 146, RULE_fieldType);
		try {
			enterOuterAlt(_localctx, 1);
			{
			setState(901);
			((FieldTypeContext)_localctx).p_1_1 = match(StellaIdent);
			setState(902);
			match(Surrogate_id_SYMB_7);
			setState(903);
			((FieldTypeContext)_localctx).p_1_3 = type();
			 ((FieldTypeContext)_localctx).result =  new stella.Absyn.AFieldType(((FieldTypeContext)_localctx).p_1_1.getText(),((FieldTypeContext)_localctx).p_1_3.result); 
			}
		}
		catch (RecognitionException re) {
			_localctx.exception = re;
			_errHandler.reportError(this, re);
			_errHandler.recover(this, re);
		}
		finally {
			exitRule();
		}
		return _localctx;
	}

	public static class ListFieldTypeContext extends ParserRuleContext {
		public stella.Absyn.ListFieldType result;
		public FieldTypeContext p_2_1;
		public FieldTypeContext p_3_1;
		public ListFieldTypeContext p_3_3;
		public FieldTypeContext fieldType() {
			return getRuleContext(FieldTypeContext.class,0);
		}
		public TerminalNode Surrogate_id_SYMB_1() { return getToken(stellaParser.Surrogate_id_SYMB_1, 0); }
		public ListFieldTypeContext listFieldType() {
			return getRuleContext(ListFieldTypeContext.class,0);
		}
		public ListFieldTypeContext(ParserRuleContext parent, int invokingState) {
			super(parent, invokingState);
		}
		@Override public int getRuleIndex() { return RULE_listFieldType; }
		@Override
		public void enterRule(ParseTreeListener listener) {
			if ( listener instanceof stellaParserListener ) ((stellaParserListener)listener).enterListFieldType(this);
		}
		@Override
		public void exitRule(ParseTreeListener listener) {
			if ( listener instanceof stellaParserListener ) ((stellaParserListener)listener).exitListFieldType(this);
		}
	}

	public final ListFieldTypeContext listFieldType() throws RecognitionException {
		ListFieldTypeContext _localctx = new ListFieldTypeContext(_ctx, getState());
		enterRule(_localctx, 148, RULE_listFieldType);
		try {
			setState(915);
			_errHandler.sync(this);
			switch ( getInterpreter().adaptivePredict(_input,31,_ctx) ) {
			case 1:
				enterOuterAlt(_localctx, 1);
				{
				 ((ListFieldTypeContext)_localctx).result =  new stella.Absyn.ListFieldType(); 
				}
				break;
			case 2:
				enterOuterAlt(_localctx, 2);
				{
				setState(907);
				((ListFieldTypeContext)_localctx).p_2_1 = fieldType();
				 ((ListFieldTypeContext)_localctx).result =  new stella.Absyn.ListFieldType(); _localctx.result.addLast(((ListFieldTypeContext)_localctx).p_2_1.result); 
				}
				break;
			case 3:
				enterOuterAlt(_localctx, 3);
				{
				setState(910);
				((ListFieldTypeContext)_localctx).p_3_1 = fieldType();
				setState(911);
				match(Surrogate_id_SYMB_1);
				setState(912);
				((ListFieldTypeContext)_localctx).p_3_3 = listFieldType();
				 ((ListFieldTypeContext)_localctx).result =  ((ListFieldTypeContext)_localctx).p_3_3.result; _localctx.result.addFirst(((ListFieldTypeContext)_localctx).p_3_1.result); 
				}
				break;
			}
		}
		catch (RecognitionException re) {
			_localctx.exception = re;
			_errHandler.reportError(this, re);
			_errHandler.recover(this, re);
		}
		finally {
			exitRule();
		}
		return _localctx;
	}

	public static class TypingContext extends ParserRuleContext {
		public stella.Absyn.Typing result;
		public ExprContext p_1_1;
		public TypeContext p_1_3;
		public TerminalNode Surrogate_id_SYMB_7() { return getToken(stellaParser.Surrogate_id_SYMB_7, 0); }
		public ExprContext expr() {
			return getRuleContext(ExprContext.class,0);
		}
		public TypeContext type() {
			return getRuleContext(TypeContext.class,0);
		}
		public TypingContext(ParserRuleContext parent, int invokingState) {
			super(parent, invokingState);
		}
		@Override public int getRuleIndex() { return RULE_typing; }
		@Override
		public void enterRule(ParseTreeListener listener) {
			if ( listener instanceof stellaParserListener ) ((stellaParserListener)listener).enterTyping(this);
		}
		@Override
		public void exitRule(ParseTreeListener listener) {
			if ( listener instanceof stellaParserListener ) ((stellaParserListener)listener).exitTyping(this);
		}
	}

	public final TypingContext typing() throws RecognitionException {
		TypingContext _localctx = new TypingContext(_ctx, getState());
		enterRule(_localctx, 150, RULE_typing);
		try {
			enterOuterAlt(_localctx, 1);
			{
			setState(917);
			((TypingContext)_localctx).p_1_1 = expr();
			setState(918);
			match(Surrogate_id_SYMB_7);
			setState(919);
			((TypingContext)_localctx).p_1_3 = type();
			 ((TypingContext)_localctx).result =  new stella.Absyn.ATyping(((TypingContext)_localctx).p_1_1.result,((TypingContext)_localctx).p_1_3.result); 
			}
		}
		catch (RecognitionException re) {
			_localctx.exception = re;
			_errHandler.reportError(this, re);
			_errHandler.recover(this, re);
		}
		finally {
			exitRule();
		}
		return _localctx;
	}

	public boolean sempred(RuleContext _localctx, int ruleIndex, int predIndex) {
		switch (ruleIndex) {
		case 42:
			return listExtension_sempred((ListExtensionContext)_localctx, predIndex);
		case 44:
			return listDecl_sempred((ListDeclContext)_localctx, predIndex);
		case 46:
			return listLocalDecl_sempred((ListLocalDeclContext)_localctx, predIndex);
		case 48:
			return listAnnotation_sempred((ListAnnotationContext)_localctx, predIndex);
		case 64:
			return expr1_sempred((Expr1Context)_localctx, predIndex);
		case 65:
			return expr2_sempred((Expr2Context)_localctx, predIndex);
		case 66:
			return expr3_sempred((Expr3Context)_localctx, predIndex);
		case 68:
			return expr5_sempred((Expr5Context)_localctx, predIndex);
		}
		return true;
	}
	private boolean listExtension_sempred(ListExtensionContext _localctx, int predIndex) {
		switch (predIndex) {
		case 0:
			return precpred(_ctx, 1);
		}
		return true;
	}
	private boolean listDecl_sempred(ListDeclContext _localctx, int predIndex) {
		switch (predIndex) {
		case 1:
			return precpred(_ctx, 1);
		}
		return true;
	}
	private boolean listLocalDecl_sempred(ListLocalDeclContext _localctx, int predIndex) {
		switch (predIndex) {
		case 2:
			return precpred(_ctx, 1);
		}
		return true;
	}
	private boolean listAnnotation_sempred(ListAnnotationContext _localctx, int predIndex) {
		switch (predIndex) {
		case 3:
			return precpred(_ctx, 1);
		}
		return true;
	}
	private boolean expr1_sempred(Expr1Context _localctx, int predIndex) {
		switch (predIndex) {
		case 4:
			return precpred(_ctx, 10);
		case 5:
			return precpred(_ctx, 3);
		case 6:
			return precpred(_ctx, 2);
		}
		return true;
	}
	private boolean expr2_sempred(Expr2Context _localctx, int predIndex) {
		switch (predIndex) {
		case 7:
			return precpred(_ctx, 3);
		case 8:
			return precpred(_ctx, 2);
		}
		return true;
	}
	private boolean expr3_sempred(Expr3Context _localctx, int predIndex) {
		switch (predIndex) {
		case 9:
			return precpred(_ctx, 2);
		}
		return true;
	}
	private boolean expr5_sempred(Expr5Context _localctx, int predIndex) {
		switch (predIndex) {
		case 10:
			return precpred(_ctx, 7);
		case 11:
			return precpred(_ctx, 6);
		}
		return true;
	}

	public static final String _serializedATN =
		"\3\u608b\ua72a\u8133\ub9ed\u417c\u3be7\u7786\u5964\3E\u039d\4\2\t\2\4"+
		"\3\t\3\4\4\t\4\4\5\t\5\4\6\t\6\4\7\t\7\4\b\t\b\4\t\t\t\4\n\t\n\4\13\t"+
		"\13\4\f\t\f\4\r\t\r\4\16\t\16\4\17\t\17\4\20\t\20\4\21\t\21\4\22\t\22"+
		"\4\23\t\23\4\24\t\24\4\25\t\25\4\26\t\26\4\27\t\27\4\30\t\30\4\31\t\31"+
		"\4\32\t\32\4\33\t\33\4\34\t\34\4\35\t\35\4\36\t\36\4\37\t\37\4 \t \4!"+
		"\t!\4\"\t\"\4#\t#\4$\t$\4%\t%\4&\t&\4\'\t\'\4(\t(\4)\t)\4*\t*\4+\t+\4"+
		",\t,\4-\t-\4.\t.\4/\t/\4\60\t\60\4\61\t\61\4\62\t\62\4\63\t\63\4\64\t"+
		"\64\4\65\t\65\4\66\t\66\4\67\t\67\48\t8\49\t9\4:\t:\4;\t;\4<\t<\4=\t="+
		"\4>\t>\4?\t?\4@\t@\4A\tA\4B\tB\4C\tC\4D\tD\4E\tE\4F\tF\4G\tG\4H\tH\4I"+
		"\tI\4J\tJ\4K\tK\4L\tL\4M\tM\3\2\3\2\3\2\3\2\3\3\3\3\3\3\3\3\3\4\3\4\3"+
		"\4\3\4\3\5\3\5\3\5\3\5\3\6\3\6\3\6\3\6\3\7\3\7\3\7\3\7\3\b\3\b\3\b\3\b"+
		"\3\t\3\t\3\t\3\t\3\n\3\n\3\n\3\n\3\13\3\13\3\13\3\13\3\f\3\f\3\f\3\f\3"+
		"\r\3\r\3\r\3\r\3\16\3\16\3\16\3\16\3\17\3\17\3\17\3\17\3\20\3\20\3\20"+
		"\3\20\3\21\3\21\3\21\3\21\3\22\3\22\3\22\3\22\3\23\3\23\3\23\3\23\3\24"+
		"\3\24\3\24\3\24\3\25\3\25\3\25\3\25\3\26\3\26\3\26\3\26\3\27\3\27\3\27"+
		"\3\27\3\30\3\30\3\30\3\30\3\31\3\31\3\31\3\31\3\32\3\32\3\32\3\32\3\33"+
		"\3\33\3\33\3\33\3\34\3\34\3\34\3\34\3\35\3\35\3\35\3\35\3\36\3\36\3\36"+
		"\3\36\3\37\3\37\3\37\3\37\3 \3 \3 \3 \3!\3!\3!\3!\3\"\3\"\3\"\3\"\3#\3"+
		"#\3#\3#\3$\3$\3$\3$\3%\3%\3%\3%\3&\3&\3&\3&\3\'\3\'\3\'\3\'\3(\3(\3(\3"+
		"(\3(\3)\3)\3)\3)\3)\3*\3*\3*\3*\3*\3+\3+\3+\3+\3+\3+\3+\3+\5+\u014a\n"+
		"+\3,\3,\3,\3,\3,\3,\3,\3,\7,\u0154\n,\f,\16,\u0157\13,\3-\3-\3-\3-\3-"+
		"\3-\3-\3-\3-\3-\3-\3-\3-\3-\3-\3-\3-\3-\3-\3-\3-\3-\5-\u016f\n-\3.\3."+
		"\3.\3.\3.\3.\3.\7.\u0178\n.\f.\16.\u017b\13.\3/\3/\3/\3\60\3\60\3\60\3"+
		"\60\3\60\3\60\3\60\3\60\7\60\u0188\n\60\f\60\16\60\u018b\13\60\3\61\3"+
		"\61\3\61\3\62\3\62\3\62\3\62\3\62\3\62\3\62\7\62\u0197\n\62\f\62\16\62"+
		"\u019a\13\62\3\63\3\63\3\63\3\63\3\63\3\64\3\64\3\64\3\64\3\64\3\64\3"+
		"\64\3\64\3\64\5\64\u01aa\n\64\3\65\3\65\3\65\3\65\3\65\5\65\u01b1\n\65"+
		"\3\66\3\66\3\66\3\66\3\66\5\66\u01b8\n\66\3\67\3\67\3\67\3\67\3\67\3\67"+
		"\3\67\3\67\3\67\3\67\3\67\3\67\3\67\3\67\3\67\3\67\3\67\3\67\3\67\5\67"+
		"\u01cd\n\67\38\38\38\38\38\38\38\38\38\58\u01d8\n8\39\39\39\39\39\3:\3"+
		":\3:\3:\3:\3:\3:\3:\3:\5:\u01e8\n:\3;\3;\3;\3;\3;\3;\3;\3;\3;\3;\3;\3"+
		";\3;\3;\3;\3;\3;\3;\3;\3;\3;\3;\3;\3;\3;\3;\3;\3;\3;\3;\3;\3;\3;\3;\3"+
		";\3;\3;\3;\3;\3;\3;\3;\3;\3;\3;\3;\3;\3;\3;\3;\5;\u021c\n;\3<\3<\3<\3"+
		"<\3<\3<\3<\3<\3<\5<\u0227\n<\3=\3=\3=\3=\3=\3>\3>\3>\3>\3>\3>\3>\3>\3"+
		">\5>\u0237\n>\3?\3?\3?\3?\3?\3@\3@\3@\3@\3@\3@\3@\3@\3@\5@\u0247\n@\3"+
		"A\3A\3A\3A\3A\3A\3A\3A\3A\3A\3A\3A\3A\3A\3A\3A\3A\3A\3A\3A\3A\3A\3A\3"+
		"A\3A\3A\3A\3A\3A\3A\5A\u0267\nA\3B\3B\3B\3B\3B\3B\3B\3B\3B\3B\3B\3B\3"+
		"B\3B\3B\3B\3B\3B\3B\3B\3B\3B\3B\3B\3B\3B\3B\3B\3B\3B\3B\3B\3B\3B\3B\3"+
		"B\3B\3B\3B\3B\3B\3B\3B\3B\3B\5B\u0296\nB\3B\3B\3B\3B\3B\3B\3B\3B\3B\3"+
		"B\3B\3B\3B\3B\3B\7B\u02a7\nB\fB\16B\u02aa\13B\3C\3C\3C\3C\3C\3C\3C\3C"+
		"\3C\3C\3C\3C\3C\3C\7C\u02ba\nC\fC\16C\u02bd\13C\3D\3D\3D\3D\3D\3D\3D\3"+
		"D\3D\3D\7D\u02c9\nD\fD\16D\u02cc\13D\3E\3E\3E\3E\3E\3E\3E\3E\3E\3E\3E"+
		"\3E\3E\3E\3E\3E\3E\3E\3E\3E\3E\3E\3E\3E\3E\3E\3E\3E\3E\3E\3E\3E\3E\3E"+
		"\3E\3E\3E\3E\3E\3E\3E\3E\3E\3E\3E\3E\3E\3E\3E\3E\3E\3E\3E\3E\3E\3E\3E"+
		"\3E\3E\3E\3E\3E\3E\3E\3E\3E\3E\3E\3E\3E\3E\3E\3E\3E\3E\3E\3E\3E\3E\3E"+
		"\3E\3E\3E\5E\u0321\nE\3F\3F\3F\3F\3F\3F\3F\3F\3F\3F\3F\3F\3F\3F\5F\u0331"+
		"\nF\3F\3F\3F\3F\3F\3F\3F\3F\7F\u033b\nF\fF\16F\u033e\13F\3G\3G\3G\3G\3"+
		"G\3G\3G\3G\3G\3G\3G\3G\3G\3G\3G\3G\3G\5G\u0351\nG\3H\3H\3H\3H\3H\3H\3"+
		"H\3H\3H\3H\3H\3H\3H\3H\3H\3H\3H\3H\3H\3H\3H\3H\3H\3H\3H\5H\u036c\nH\3"+
		"I\3I\3I\3I\3I\3I\3I\3I\3I\3I\3I\3I\3I\5I\u037b\nI\3J\3J\3J\3J\3J\3J\3"+
		"J\3J\3J\5J\u0386\nJ\3K\3K\3K\3K\3K\3L\3L\3L\3L\3L\3L\3L\3L\3L\5L\u0396"+
		"\nL\3M\3M\3M\3M\3M\3M\2\nVZ^b\u0082\u0084\u0086\u008aN\2\4\6\b\n\f\16"+
		"\20\22\24\26\30\32\34\36 \"$&(*,.\60\62\64\668:<>@BDFHJLNPRTVXZ\\^`bd"+
		"fhjlnprtvxz|~\u0080\u0082\u0084\u0086\u0088\u008a\u008c\u008e\u0090\u0092"+
		"\u0094\u0096\u0098\2\2\2\u03a2\2\u009a\3\2\2\2\4\u009e\3\2\2\2\6\u00a2"+
		"\3\2\2\2\b\u00a6\3\2\2\2\n\u00aa\3\2\2\2\f\u00ae\3\2\2\2\16\u00b2\3\2"+
		"\2\2\20\u00b6\3\2\2\2\22\u00ba\3\2\2\2\24\u00be\3\2\2\2\26\u00c2\3\2\2"+
		"\2\30\u00c6\3\2\2\2\32\u00ca\3\2\2\2\34\u00ce\3\2\2\2\36\u00d2\3\2\2\2"+
		" \u00d6\3\2\2\2\"\u00da\3\2\2\2$\u00de\3\2\2\2&\u00e2\3\2\2\2(\u00e6\3"+
		"\2\2\2*\u00ea\3\2\2\2,\u00ee\3\2\2\2.\u00f2\3\2\2\2\60\u00f6\3\2\2\2\62"+
		"\u00fa\3\2\2\2\64\u00fe\3\2\2\2\66\u0102\3\2\2\28\u0106\3\2\2\2:\u010a"+
		"\3\2\2\2<\u010e\3\2\2\2>\u0112\3\2\2\2@\u0116\3\2\2\2B\u011a\3\2\2\2D"+
		"\u011e\3\2\2\2F\u0122\3\2\2\2H\u0126\3\2\2\2J\u012a\3\2\2\2L\u012e\3\2"+
		"\2\2N\u0132\3\2\2\2P\u0137\3\2\2\2R\u013c\3\2\2\2T\u0149\3\2\2\2V\u014b"+
		"\3\2\2\2X\u016e\3\2\2\2Z\u0170\3\2\2\2\\\u017c\3\2\2\2^\u017f\3\2\2\2"+
		"`\u018c\3\2\2\2b\u018f\3\2\2\2d\u019b\3\2\2\2f\u01a9\3\2\2\2h\u01b0\3"+
		"\2\2\2j\u01b7\3\2\2\2l\u01cc\3\2\2\2n\u01d7\3\2\2\2p\u01d9\3\2\2\2r\u01e7"+
		"\3\2\2\2t\u021b\3\2\2\2v\u0226\3\2\2\2x\u0228\3\2\2\2z\u0236\3\2\2\2|"+
		"\u0238\3\2\2\2~\u0246\3\2\2\2\u0080\u0266\3\2\2\2\u0082\u0295\3\2\2\2"+
		"\u0084\u02ab\3\2\2\2\u0086\u02be\3\2\2\2\u0088\u0320\3\2\2\2\u008a\u0330"+
		"\3\2\2\2\u008c\u0350\3\2\2\2\u008e\u036b\3\2\2\2\u0090\u037a\3\2\2\2\u0092"+
		"\u0385\3\2\2\2\u0094\u0387\3\2\2\2\u0096\u0395\3\2\2\2\u0098\u0397\3\2"+
		"\2\2\u009a\u009b\5N(\2\u009b\u009c\7\2\2\3\u009c\u009d\b\2\1\2\u009d\3"+
		"\3\2\2\2\u009e\u009f\5P)\2\u009f\u00a0\7\2\2\3\u00a0\u00a1\b\3\1\2\u00a1"+
		"\5\3\2\2\2\u00a2\u00a3\5R*\2\u00a3\u00a4\7\2\2\3\u00a4\u00a5\b\4\1\2\u00a5"+
		"\7\3\2\2\2\u00a6\u00a7\5T+\2\u00a7\u00a8\7\2\2\3\u00a8\u00a9\b\5\1\2\u00a9"+
		"\t\3\2\2\2\u00aa\u00ab\5V,\2\u00ab\u00ac\7\2\2\3\u00ac\u00ad\b\6\1\2\u00ad"+
		"\13\3\2\2\2\u00ae\u00af\5X-\2\u00af\u00b0\7\2\2\3\u00b0\u00b1\b\7\1\2"+
		"\u00b1\r\3\2\2\2\u00b2\u00b3\5Z.\2\u00b3\u00b4\7\2\2\3\u00b4\u00b5\b\b"+
		"\1\2\u00b5\17\3\2\2\2\u00b6\u00b7\5\\/\2\u00b7\u00b8\7\2\2\3\u00b8\u00b9"+
		"\b\t\1\2\u00b9\21\3\2\2\2\u00ba\u00bb\5^\60\2\u00bb\u00bc\7\2\2\3\u00bc"+
		"\u00bd\b\n\1\2\u00bd\23\3\2\2\2\u00be\u00bf\5`\61\2\u00bf\u00c0\7\2\2"+
		"\3\u00c0\u00c1\b\13\1\2\u00c1\25\3\2\2\2\u00c2\u00c3\5b\62\2\u00c3\u00c4"+
		"\7\2\2\3\u00c4\u00c5\b\f\1\2\u00c5\27\3\2\2\2\u00c6\u00c7\5d\63\2\u00c7"+
		"\u00c8\7\2\2\3\u00c8\u00c9\b\r\1\2\u00c9\31\3\2\2\2\u00ca\u00cb\5f\64"+
		"\2\u00cb\u00cc\7\2\2\3\u00cc\u00cd\b\16\1\2\u00cd\33\3\2\2\2\u00ce\u00cf"+
		"\5h\65\2\u00cf\u00d0\7\2\2\3\u00d0\u00d1\b\17\1\2\u00d1\35\3\2\2\2\u00d2"+
		"\u00d3\5j\66\2\u00d3\u00d4\7\2\2\3\u00d4\u00d5\b\20\1\2\u00d5\37\3\2\2"+
		"\2\u00d6\u00d7\5l\67\2\u00d7\u00d8\7\2\2\3\u00d8\u00d9\b\21\1\2\u00d9"+
		"!\3\2\2\2\u00da\u00db\5n8\2\u00db\u00dc\7\2\2\3\u00dc\u00dd\b\22\1\2\u00dd"+
		"#\3\2\2\2\u00de\u00df\5p9\2\u00df\u00e0\7\2\2\3\u00e0\u00e1\b\23\1\2\u00e1"+
		"%\3\2\2\2\u00e2\u00e3\5r:\2\u00e3\u00e4\7\2\2\3\u00e4\u00e5\b\24\1\2\u00e5"+
		"\'\3\2\2\2\u00e6\u00e7\5t;\2\u00e7\u00e8\7\2\2\3\u00e8\u00e9\b\25\1\2"+
		"\u00e9)\3\2\2\2\u00ea\u00eb\5v<\2\u00eb\u00ec\7\2\2\3\u00ec\u00ed\b\26"+
		"\1\2\u00ed+\3\2\2\2\u00ee\u00ef\5x=\2\u00ef\u00f0\7\2\2\3\u00f0\u00f1"+
		"\b\27\1\2\u00f1-\3\2\2\2\u00f2\u00f3\5z>\2\u00f3\u00f4\7\2\2\3\u00f4\u00f5"+
		"\b\30\1\2\u00f5/\3\2\2\2\u00f6\u00f7\5|?\2\u00f7\u00f8\7\2\2\3\u00f8\u00f9"+
		"\b\31\1\2\u00f9\61\3\2\2\2\u00fa\u00fb\5~@\2\u00fb\u00fc\7\2\2\3\u00fc"+
		"\u00fd\b\32\1\2\u00fd\63\3\2\2\2\u00fe\u00ff\5\u0080A\2\u00ff\u0100\7"+
		"\2\2\3\u0100\u0101\b\33\1\2\u0101\65\3\2\2\2\u0102\u0103\5\u0082B\2\u0103"+
		"\u0104\7\2\2\3\u0104\u0105\b\34\1\2\u0105\67\3\2\2\2\u0106\u0107\5\u0084"+
		"C\2\u0107\u0108\7\2\2\3\u0108\u0109\b\35\1\2\u01099\3\2\2\2\u010a\u010b"+
		"\5\u0086D\2\u010b\u010c\7\2\2\3\u010c\u010d\b\36\1\2\u010d;\3\2\2\2\u010e"+
		"\u010f\5\u0088E\2\u010f\u0110\7\2\2\3\u0110\u0111\b\37\1\2\u0111=\3\2"+
		"\2\2\u0112\u0113\5\u008aF\2\u0113\u0114\7\2\2\3\u0114\u0115\b \1\2\u0115"+
		"?\3\2\2\2\u0116\u0117\5\u008cG\2\u0117\u0118\7\2\2\3\u0118\u0119\b!\1"+
		"\2\u0119A\3\2\2\2\u011a\u011b\5\u008eH\2\u011b\u011c\7\2\2\3\u011c\u011d"+
		"\b\"\1\2\u011dC\3\2\2\2\u011e\u011f\5\u0090I\2\u011f\u0120\7\2\2\3\u0120"+
		"\u0121\b#\1\2\u0121E\3\2\2\2\u0122\u0123\5\u0092J\2\u0123\u0124\7\2\2"+
		"\3\u0124\u0125\b$\1\2\u0125G\3\2\2\2\u0126\u0127\5\u0094K\2\u0127\u0128"+
		"\7\2\2\3\u0128\u0129\b%\1\2\u0129I\3\2\2\2\u012a\u012b\5\u0096L\2\u012b"+
		"\u012c\7\2\2\3\u012c\u012d\b&\1\2\u012dK\3\2\2\2\u012e\u012f\5\u0098M"+
		"\2\u012f\u0130\7\2\2\3\u0130\u0131\b\'\1\2\u0131M\3\2\2\2\u0132\u0133"+
		"\5P)\2\u0133\u0134\5V,\2\u0134\u0135\5Z.\2\u0135\u0136\b(\1\2\u0136O\3"+
		"\2\2\2\u0137\u0138\7.\2\2\u0138\u0139\7$\2\2\u0139\u013a\7\3\2\2\u013a"+
		"\u013b\b)\1\2\u013bQ\3\2\2\2\u013c\u013d\7&\2\2\u013d\u013e\7=\2\2\u013e"+
		"\u013f\5T+\2\u013f\u0140\b*\1\2\u0140S\3\2\2\2\u0141\u014a\b+\1\2\u0142"+
		"\u0143\7B\2\2\u0143\u014a\b+\1\2\u0144\u0145\7B\2\2\u0145\u0146\7\4\2"+
		"\2\u0146\u0147\5T+\2\u0147\u0148\b+\1\2\u0148\u014a\3\2\2\2\u0149\u0141"+
		"\3\2\2\2\u0149\u0142\3\2\2\2\u0149\u0144\3\2\2\2\u014aU\3\2\2\2\u014b"+
		"\u014c\b,\1\2\u014c\u014d\b,\1\2\u014d\u0155\3\2\2\2\u014e\u014f\f\3\2"+
		"\2\u014f\u0150\5R*\2\u0150\u0151\7\3\2\2\u0151\u0152\b,\1\2\u0152\u0154"+
		"\3\2\2\2\u0153\u014e\3\2\2\2\u0154\u0157\3\2\2\2\u0155\u0153\3\2\2\2\u0155"+
		"\u0156\3\2\2\2\u0156W\3\2\2\2\u0157\u0155\3\2\2\2\u0158\u0159\5b\62\2"+
		"\u0159\u015a\7)\2\2\u015a\u015b\7A\2\2\u015b\u015c\7\5\2\2\u015c\u015d"+
		"\5f\64\2\u015d\u015e\7\6\2\2\u015e\u015f\5h\65\2\u015f\u0160\5j\66\2\u0160"+
		"\u0161\7\7\2\2\u0161\u0162\5Z.\2\u0162\u0163\7\64\2\2\u0163\u0164\5l\67"+
		"\2\u0164\u0165\7\3\2\2\u0165\u0166\7\b\2\2\u0166\u0167\b-\1\2\u0167\u016f"+
		"\3\2\2\2\u0168\u0169\7:\2\2\u0169\u016a\7A\2\2\u016a\u016b\7\t\2\2\u016b"+
		"\u016c\5\u008cG\2\u016c\u016d\b-\1\2\u016d\u016f\3\2\2\2\u016e\u0158\3"+
		"\2\2\2\u016e\u0168\3\2\2\2\u016fY\3\2\2\2\u0170\u0171\b.\1\2\u0171\u0172"+
		"\b.\1\2\u0172\u0179\3\2\2\2\u0173\u0174\f\3\2\2\u0174\u0175\5X-\2\u0175"+
		"\u0176\b.\1\2\u0176\u0178\3\2\2\2\u0177\u0173\3\2\2\2\u0178\u017b\3\2"+
		"\2\2\u0179\u0177\3\2\2\2\u0179\u017a\3\2\2\2\u017a[\3\2\2\2\u017b\u0179"+
		"\3\2\2\2\u017c\u017d\5X-\2\u017d\u017e\b/\1\2\u017e]\3\2\2\2\u017f\u0180"+
		"\b\60\1\2\u0180\u0181\b\60\1\2\u0181\u0189\3\2\2\2\u0182\u0183\f\3\2\2"+
		"\u0183\u0184\5\\/\2\u0184\u0185\7\3\2\2\u0185\u0186\b\60\1\2\u0186\u0188"+
		"\3\2\2\2\u0187\u0182\3\2\2\2\u0188\u018b\3\2\2\2\u0189\u0187\3\2\2\2\u0189"+
		"\u018a\3\2\2\2\u018a_\3\2\2\2\u018b\u0189\3\2\2\2\u018c\u018d\7-\2\2\u018d"+
		"\u018e\b\61\1\2\u018ea\3\2\2\2\u018f\u0190\b\62\1\2\u0190\u0191\b\62\1"+
		"\2\u0191\u0198\3\2\2\2\u0192\u0193\f\3\2\2\u0193\u0194\5`\61\2\u0194\u0195"+
		"\b\62\1\2\u0195\u0197\3\2\2\2\u0196\u0192\3\2\2\2\u0197\u019a\3\2\2\2"+
		"\u0198\u0196\3\2\2\2\u0198\u0199\3\2\2\2\u0199c\3\2\2\2\u019a\u0198\3"+
		"\2\2\2\u019b\u019c\7A\2\2\u019c\u019d\7\n\2\2\u019d\u019e\5\u008cG\2\u019e"+
		"\u019f\b\63\1\2\u019fe\3\2\2\2\u01a0\u01aa\b\64\1\2\u01a1\u01a2\5d\63"+
		"\2\u01a2\u01a3\b\64\1\2\u01a3\u01aa\3\2\2\2\u01a4\u01a5\5d\63\2\u01a5"+
		"\u01a6\7\4\2\2\u01a6\u01a7\5f\64\2\u01a7\u01a8\b\64\1\2\u01a8\u01aa\3"+
		"\2\2\2\u01a9\u01a0\3\2\2\2\u01a9\u01a1\3\2\2\2\u01a9\u01a4\3\2\2\2\u01aa"+
		"g\3\2\2\2\u01ab\u01b1\b\65\1\2\u01ac\u01ad\7\13\2\2\u01ad\u01ae\5\u008c"+
		"G\2\u01ae\u01af\b\65\1\2\u01af\u01b1\3\2\2\2\u01b0\u01ab\3\2\2\2\u01b0"+
		"\u01ac\3\2\2\2\u01b1i\3\2\2\2\u01b2\u01b8\b\66\1\2\u01b3\u01b4\78\2\2"+
		"\u01b4\u01b5\5\u0092J\2\u01b5\u01b6\b\66\1\2\u01b6\u01b8\3\2\2\2\u01b7"+
		"\u01b2\3\2\2\2\u01b7\u01b3\3\2\2\2\u01b8k\3\2\2\2\u01b9\u01ba\7+\2\2\u01ba"+
		"\u01bb\5l\67\2\u01bb\u01bc\7\67\2\2\u01bc\u01bd\5l\67\2\u01bd\u01be\7"+
		"%\2\2\u01be\u01bf\5l\67\2\u01bf\u01c0\b\67\1\2\u01c0\u01cd\3\2\2\2\u01c1"+
		"\u01c2\7/\2\2\u01c2\u01c3\7A\2\2\u01c3\u01c4\7\t\2\2\u01c4\u01c5\5l\67"+
		"\2\u01c5\u01c6\7,\2\2\u01c6\u01c7\5l\67\2\u01c7\u01c8\b\67\1\2\u01c8\u01cd"+
		"\3\2\2\2\u01c9\u01ca\5\u0082B\2\u01ca\u01cb\b\67\1\2\u01cb\u01cd\3\2\2"+
		"\2\u01cc\u01b9\3\2\2\2\u01cc\u01c1\3\2\2\2\u01cc\u01c9\3\2\2\2\u01cdm"+
		"\3\2\2\2\u01ce\u01d8\b8\1\2\u01cf\u01d0\5l\67\2\u01d0\u01d1\b8\1\2\u01d1"+
		"\u01d8\3\2\2\2\u01d2\u01d3\5l\67\2\u01d3\u01d4\7\4\2\2\u01d4\u01d5\5n"+
		"8\2\u01d5\u01d6\b8\1\2\u01d6\u01d8\3\2\2\2\u01d7\u01ce\3\2\2\2\u01d7\u01cf"+
		"\3\2\2\2\u01d7\u01d2\3\2\2\2\u01d8o\3\2\2\2\u01d9\u01da\5t;\2\u01da\u01db"+
		"\7\f\2\2\u01db\u01dc\5l\67\2\u01dc\u01dd\b9\1\2\u01ddq\3\2\2\2\u01de\u01e8"+
		"\b:\1\2\u01df\u01e0\5p9\2\u01e0\u01e1\b:\1\2\u01e1\u01e8\3\2\2\2\u01e2"+
		"\u01e3\5p9\2\u01e3\u01e4\7\3\2\2\u01e4\u01e5\5r:\2\u01e5\u01e6\b:\1\2"+
		"\u01e6\u01e8\3\2\2\2\u01e7\u01de\3\2\2\2\u01e7\u01df\3\2\2\2\u01e7\u01e2"+
		"\3\2\2\2\u01e8s\3\2\2\2\u01e9\u01ea\7\r\2\2\u01ea\u01eb\7A\2\2\u01eb\u01ec"+
		"\7\t\2\2\u01ec\u01ed\5t;\2\u01ed\u01ee\7\16\2\2\u01ee\u01ef\b;\1\2\u01ef"+
		"\u021c\3\2\2\2\u01f0\u01f1\7\7\2\2\u01f1\u01f2\5v<\2\u01f2\u01f3\7\b\2"+
		"\2\u01f3\u01f4\b;\1\2\u01f4\u021c\3\2\2\2\u01f5\u01f6\7\63\2\2\u01f6\u01f7"+
		"\7\7\2\2\u01f7\u01f8\5z>\2\u01f8\u01f9\7\b\2\2\u01f9\u01fa\b;\1\2\u01fa"+
		"\u021c\3\2\2\2\u01fb\u01fc\7\17\2\2\u01fc\u01fd\5v<\2\u01fd\u01fe\7\20"+
		"\2\2\u01fe\u01ff\b;\1\2\u01ff\u021c\3\2\2\2\u0200\u0201\7#\2\2\u0201\u0202"+
		"\7\5\2\2\u0202\u0203\5t;\2\u0203\u0204\7\4\2\2\u0204\u0205\5t;\2\u0205"+
		"\u0206\7\6\2\2\u0206\u0207\b;\1\2\u0207\u021c\3\2\2\2\u0208\u0209\7\'"+
		"\2\2\u0209\u021c\b;\1\2\u020a\u020b\79\2\2\u020b\u021c\b;\1\2\u020c\u020d"+
		"\7C\2\2\u020d\u021c\b;\1\2\u020e\u020f\7\66\2\2\u020f\u0210\7\5\2\2\u0210"+
		"\u0211\5t;\2\u0211\u0212\7\6\2\2\u0212\u0213\b;\1\2\u0213\u021c\3\2\2"+
		"\2\u0214\u0215\7A\2\2\u0215\u021c\b;\1\2\u0216\u0217\7\5\2\2\u0217\u0218"+
		"\5t;\2\u0218\u0219\7\6\2\2\u0219\u021a\b;\1\2\u021a\u021c\3\2\2\2\u021b"+
		"\u01e9\3\2\2\2\u021b\u01f0\3\2\2\2\u021b\u01f5\3\2\2\2\u021b\u01fb\3\2"+
		"\2\2\u021b\u0200\3\2\2\2\u021b\u0208\3\2\2\2\u021b\u020a\3\2\2\2\u021b"+
		"\u020c\3\2\2\2\u021b\u020e\3\2\2\2\u021b\u0214\3\2\2\2\u021b\u0216\3\2"+
		"\2\2\u021cu\3\2\2\2\u021d\u0227\b<\1\2\u021e\u021f\5t;\2\u021f\u0220\b"+
		"<\1\2\u0220\u0227\3\2\2\2\u0221\u0222\5t;\2\u0222\u0223\7\4\2\2\u0223"+
		"\u0224\5v<\2\u0224\u0225\b<\1\2\u0225\u0227\3\2\2\2\u0226\u021d\3\2\2"+
		"\2\u0226\u021e\3\2\2\2\u0226\u0221\3\2\2\2\u0227w\3\2\2\2\u0228\u0229"+
		"\7A\2\2\u0229\u022a\7\t\2\2\u022a\u022b\5t;\2\u022b\u022c\b=\1\2\u022c"+
		"y\3\2\2\2\u022d\u0237\b>\1\2\u022e\u022f\5x=\2\u022f\u0230\b>\1\2\u0230"+
		"\u0237\3\2\2\2\u0231\u0232\5x=\2\u0232\u0233\7\4\2\2\u0233\u0234\5z>\2"+
		"\u0234\u0235\b>\1\2\u0235\u0237\3\2\2\2\u0236\u022d\3\2\2\2\u0236\u022e"+
		"\3\2\2\2\u0236\u0231\3\2\2\2\u0237{\3\2\2\2\u0238\u0239\7A\2\2\u0239\u023a"+
		"\7\t\2\2\u023a\u023b\5l\67\2\u023b\u023c\b?\1\2\u023c}\3\2\2\2\u023d\u0247"+
		"\b@\1\2\u023e\u023f\5|?\2\u023f\u0240\b@\1\2\u0240\u0247\3\2\2\2\u0241"+
		"\u0242\5|?\2\u0242\u0243\7\4\2\2\u0243\u0244\5~@\2\u0244\u0245\b@\1\2"+
		"\u0245\u0247\3\2\2\2\u0246\u023d\3\2\2\2\u0246\u023e\3\2\2\2\u0246\u0241"+
		"\3\2\2\2\u0247\177\3\2\2\2\u0248\u0249\5\u0082B\2\u0249\u024a\7\r\2\2"+
		"\u024a\u024b\5\u0082B\2\u024b\u024c\bA\1\2\u024c\u0267\3\2\2\2\u024d\u024e"+
		"\5\u0082B\2\u024e\u024f\7\21\2\2\u024f\u0250\5\u0082B\2\u0250\u0251\b"+
		"A\1\2\u0251\u0267\3\2\2\2\u0252\u0253\5\u0082B\2\u0253\u0254\7\16\2\2"+
		"\u0254\u0255\5\u0082B\2\u0255\u0256\bA\1\2\u0256\u0267\3\2\2\2\u0257\u0258"+
		"\5\u0082B\2\u0258\u0259\7\22\2\2\u0259\u025a\5\u0082B\2\u025a\u025b\b"+
		"A\1\2\u025b\u0267\3\2\2\2\u025c\u025d\5\u0082B\2\u025d\u025e\7\23\2\2"+
		"\u025e\u025f\5\u0082B\2\u025f\u0260\bA\1\2\u0260\u0267\3\2\2\2\u0261\u0262"+
		"\5\u0082B\2\u0262\u0263\7\24\2\2\u0263\u0264\5\u0082B\2\u0264\u0265\b"+
		"A\1\2\u0265\u0267\3\2\2\2\u0266\u0248\3\2\2\2\u0266\u024d\3\2\2\2\u0266"+
		"\u0252\3\2\2\2\u0266\u0257\3\2\2\2\u0266\u025c\3\2\2\2\u0266\u0261\3\2"+
		"\2\2\u0267\u0081\3\2\2\2\u0268\u0269\bB\1\2\u0269\u026a\7)\2\2\u026a\u026b"+
		"\7\5\2\2\u026b\u026c\5f\64\2\u026c\u026d\7\6\2\2\u026d\u026e\7\7\2\2\u026e"+
		"\u026f\7\64\2\2\u026f\u0270\5l\67\2\u0270\u0271\7\3\2\2\u0271\u0272\7"+
		"\b\2\2\u0272\u0273\bB\1\2\u0273\u0296\3\2\2\2\u0274\u0275\7\7\2\2\u0275"+
		"\u0276\5n8\2\u0276\u0277\7\b\2\2\u0277\u0278\bB\1\2\u0278\u0296\3\2\2"+
		"\2\u0279\u027a\7\63\2\2\u027a\u027b\7\7\2\2\u027b\u027c\5~@\2\u027c\u027d"+
		"\7\b\2\2\u027d\u027e\bB\1\2\u027e\u0296\3\2\2\2\u027f\u0280\7\r\2\2\u0280"+
		"\u0281\7A\2\2\u0281\u0282\7\t\2\2\u0282\u0283\5l\67\2\u0283\u0284\7\16"+
		"\2\2\u0284\u0285\bB\1\2\u0285\u0296\3\2\2\2\u0286\u0287\7\60\2\2\u0287"+
		"\u0288\5\u0082B\2\u0288\u0289\7\7\2\2\u0289\u028a\5r:\2\u028a\u028b\7"+
		"\b\2\2\u028b\u028c\bB\1\2\u028c\u0296\3\2\2\2\u028d\u028e\7\17\2\2\u028e"+
		"\u028f\5n8\2\u028f\u0290\7\20\2\2\u0290\u0291\bB\1\2\u0291\u0296\3\2\2"+
		"\2\u0292\u0293\5\u0084C\2\u0293\u0294\bB\1\2\u0294\u0296\3\2\2\2\u0295"+
		"\u0268\3\2\2\2\u0295\u0274\3\2\2\2\u0295\u0279\3\2\2\2\u0295\u027f\3\2"+
		"\2\2\u0295\u0286\3\2\2\2\u0295\u028d\3\2\2\2\u0295\u0292\3\2\2\2\u0296"+
		"\u02a8\3\2\2\2\u0297\u0298\f\f\2\2\u0298\u0299\7\"\2\2\u0299\u029a\5\u008c"+
		"G\2\u029a\u029b\bB\1\2\u029b\u02a7\3\2\2\2\u029c\u029d\f\5\2\2\u029d\u029e"+
		"\7\25\2\2\u029e\u029f\5\u0084C\2\u029f\u02a0\bB\1\2\u02a0\u02a7\3\2\2"+
		"\2\u02a1\u02a2\f\4\2\2\u02a2\u02a3\7\62\2\2\u02a3\u02a4\5\u0084C\2\u02a4"+
		"\u02a5\bB\1\2\u02a5\u02a7\3\2\2\2\u02a6\u0297\3\2\2\2\u02a6\u029c\3\2"+
		"\2\2\u02a6\u02a1\3\2\2\2\u02a7\u02aa\3\2\2\2\u02a8\u02a6\3\2\2\2\u02a8"+
		"\u02a9\3\2\2\2\u02a9\u0083\3\2\2\2\u02aa\u02a8\3\2\2\2\u02ab\u02ac\bC"+
		"\1\2\u02ac\u02ad\5\u0086D\2\u02ad\u02ae\bC\1\2\u02ae\u02bb\3\2\2\2\u02af"+
		"\u02b0\f\5\2\2\u02b0\u02b1\7\26\2\2\u02b1\u02b2\5\u0086D\2\u02b2\u02b3"+
		"\bC\1\2\u02b3\u02ba\3\2\2\2\u02b4\u02b5\f\4\2\2\u02b5\u02b6\7!\2\2\u02b6"+
		"\u02b7\5\u0086D\2\u02b7\u02b8\bC\1\2\u02b8\u02ba\3\2\2\2\u02b9\u02af\3"+
		"\2\2\2\u02b9\u02b4\3\2\2\2\u02ba\u02bd\3\2\2\2\u02bb\u02b9\3\2\2\2\u02bb"+
		"\u02bc\3\2\2\2\u02bc\u0085\3\2\2\2\u02bd\u02bb\3\2\2\2\u02be\u02bf\bD"+
		"\1\2\u02bf\u02c0\5\u0088E\2\u02c0\u02c1\bD\1\2\u02c1\u02ca\3\2\2\2\u02c2"+
		"\u02c3\f\4\2\2\u02c3\u02c4\7\5\2\2\u02c4\u02c5\5n8\2\u02c5\u02c6\7\6\2"+
		"\2\u02c6\u02c7\bD\1\2\u02c7\u02c9\3\2\2\2\u02c8\u02c2\3\2\2\2\u02c9\u02cc"+
		"\3\2\2\2\u02ca\u02c8\3\2\2\2\u02ca\u02cb\3\2\2\2\u02cb\u0087\3\2\2\2\u02cc"+
		"\u02ca\3\2\2\2\u02cd\u02ce\7#\2\2\u02ce\u02cf\7\5\2\2\u02cf\u02d0\5l\67"+
		"\2\u02d0\u02d1\7\4\2\2\u02d1\u02d2\5l\67\2\u02d2\u02d3\7\6\2\2\u02d3\u02d4"+
		"\bE\1\2\u02d4\u0321\3\2\2\2\u02d5\u02d6\7\27\2\2\u02d6\u02d7\7\5\2\2\u02d7"+
		"\u02d8\5l\67\2\u02d8\u02d9\7\6\2\2\u02d9\u02da\bE\1\2\u02da\u0321\3\2"+
		"\2\2\u02db\u02dc\7\30\2\2\u02dc\u02dd\7\5\2\2\u02dd\u02de\5l\67\2\u02de"+
		"\u02df\7\6\2\2\u02df\u02e0\bE\1\2\u02e0\u0321\3\2\2\2\u02e1\u02e2\7\31"+
		"\2\2\u02e2\u02e3\7\5\2\2\u02e3\u02e4\5l\67\2\u02e4\u02e5\7\6\2\2\u02e5"+
		"\u02e6\bE\1\2\u02e6\u0321\3\2\2\2\u02e7\u02e8\7\66\2\2\u02e8\u02e9\7\5"+
		"\2\2\u02e9\u02ea\5l\67\2\u02ea\u02eb\7\6\2\2\u02eb\u02ec\bE\1\2\u02ec"+
		"\u0321\3\2\2\2\u02ed\u02ee\7\61\2\2\u02ee\u02ef\7\5\2\2\u02ef\u02f0\5"+
		"l\67\2\u02f0\u02f1\7\6\2\2\u02f1\u02f2\bE\1\2\u02f2\u0321\3\2\2\2\u02f3"+
		"\u02f4\7\32\2\2\u02f4\u02f5\7\5\2\2\u02f5\u02f6\5l\67\2\u02f6\u02f7\7"+
		"\6\2\2\u02f7\u02f8\bE\1\2\u02f8\u0321\3\2\2\2\u02f9\u02fa\7\33\2\2\u02fa"+
		"\u02fb\7\5\2\2\u02fb\u02fc\5l\67\2\u02fc\u02fd\7\6\2\2\u02fd\u02fe\bE"+
		"\1\2\u02fe\u0321\3\2\2\2\u02ff\u0300\7(\2\2\u0300\u0301\7\5\2\2\u0301"+
		"\u0302\5l\67\2\u0302\u0303\7\6\2\2\u0303\u0304\bE\1\2\u0304\u0321\3\2"+
		"\2\2\u0305\u0306\7\34\2\2\u0306\u0307\7\5\2\2\u0307\u0308\5l\67\2\u0308"+
		"\u0309\7\4\2\2\u0309\u030a\5l\67\2\u030a\u030b\7\4\2\2\u030b\u030c\5l"+
		"\67\2\u030c\u030d\7\6\2\2\u030d\u030e\bE\1\2\u030e\u0321\3\2\2\2\u030f"+
		"\u0310\7*\2\2\u0310\u0311\7\17\2\2\u0311\u0312\5\u008cG\2\u0312\u0313"+
		"\7\20\2\2\u0313\u0314\5\u008aF\2\u0314\u0315\bE\1\2\u0315\u0321\3\2\2"+
		"\2\u0316\u0317\7;\2\2\u0317\u0318\7\17\2\2\u0318\u0319\5\u008cG\2\u0319"+
		"\u031a\7\20\2\2\u031a\u031b\5\u008aF\2\u031b\u031c\bE\1\2\u031c\u0321"+
		"\3\2\2\2\u031d\u031e\5\u008aF\2\u031e\u031f\bE\1\2\u031f\u0321\3\2\2\2"+
		"\u0320\u02cd\3\2\2\2\u0320\u02d5\3\2\2\2\u0320\u02db\3\2\2\2\u0320\u02e1"+
		"\3\2\2\2\u0320\u02e7\3\2\2\2\u0320\u02ed\3\2\2\2\u0320\u02f3\3\2\2\2\u0320"+
		"\u02f9\3\2\2\2\u0320\u02ff\3\2\2\2\u0320\u0305\3\2\2\2\u0320\u030f\3\2"+
		"\2\2\u0320\u0316\3\2\2\2\u0320\u031d\3\2\2\2\u0321\u0089\3\2\2\2\u0322"+
		"\u0323\bF\1\2\u0323\u0324\79\2\2\u0324\u0331\bF\1\2\u0325\u0326\7\'\2"+
		"\2\u0326\u0331\bF\1\2\u0327\u0328\7C\2\2\u0328\u0331\bF\1\2\u0329\u032a"+
		"\7A\2\2\u032a\u0331\bF\1\2\u032b\u032c\7\5\2\2\u032c\u032d\5l\67\2\u032d"+
		"\u032e\7\6\2\2\u032e\u032f\bF\1\2\u032f\u0331\3\2\2\2\u0330\u0322\3\2"+
		"\2\2\u0330\u0325\3\2\2\2\u0330\u0327\3\2\2\2\u0330\u0329\3\2\2\2\u0330"+
		"\u032b\3\2\2\2\u0331\u033c\3\2\2\2\u0332\u0333\f\t\2\2\u0333\u0334\7\35"+
		"\2\2\u0334\u0335\7A\2\2\u0335\u033b\bF\1\2\u0336\u0337\f\b\2\2\u0337\u0338"+
		"\7\35\2\2\u0338\u0339\7C\2\2\u0339\u033b\bF\1\2\u033a\u0332\3\2\2\2\u033a"+
		"\u0336\3\2\2\2\u033b\u033e\3\2\2\2\u033c\u033a\3\2\2\2\u033c\u033d\3\2"+
		"\2\2\u033d\u008b\3\2\2\2\u033e\u033c\3\2\2\2\u033f\u0340\7)\2\2\u0340"+
		"\u0341\7\5\2\2\u0341\u0342\5\u0092J\2\u0342\u0343\7\6\2\2\u0343\u0344"+
		"\7\13\2\2\u0344\u0345\5\u008cG\2\u0345\u0346\bG\1\2\u0346\u0351\3\2\2"+
		"\2\u0347\u0348\7>\2\2\u0348\u0349\7A\2\2\u0349\u034a\7\35\2\2\u034a\u034b"+
		"\5\u008cG\2\u034b\u034c\bG\1\2\u034c\u0351\3\2\2\2\u034d\u034e\5\u008e"+
		"H\2\u034e\u034f\bG\1\2\u034f\u0351\3\2\2\2\u0350\u033f\3\2\2\2\u0350\u0347"+
		"\3\2\2\2\u0350\u034d\3\2\2\2\u0351\u008d\3\2\2\2\u0352\u0353\7\7\2\2\u0353"+
		"\u0354\5\u0092J\2\u0354\u0355\7\b\2\2\u0355\u0356\bH\1\2\u0356\u036c\3"+
		"\2\2\2\u0357\u0358\7\65\2\2\u0358\u0359\7\7\2\2\u0359\u035a\5\u0096L\2"+
		"\u035a\u035b\7\b\2\2\u035b\u035c\bH\1\2\u035c\u036c\3\2\2\2\u035d\u035e"+
		"\7<\2\2\u035e\u035f\7\r\2\2\u035f\u0360\5\u0096L\2\u0360\u0361\7\16\2"+
		"\2\u0361\u0362\bH\1\2\u0362\u036c\3\2\2\2\u0363\u0364\7\17\2\2\u0364\u0365"+
		"\5\u008cG\2\u0365\u0366\7\20\2\2\u0366\u0367\bH\1\2\u0367\u036c\3\2\2"+
		"\2\u0368\u0369\5\u0090I\2\u0369\u036a\bH\1\2\u036a\u036c\3\2\2\2\u036b"+
		"\u0352\3\2\2\2\u036b\u0357\3\2\2\2\u036b\u035d\3\2\2\2\u036b\u0363\3\2"+
		"\2\2\u036b\u0368\3\2\2\2\u036c\u008f\3\2\2\2\u036d\u036e\7\36\2\2\u036e"+
		"\u037b\bI\1\2\u036f\u0370\7\37\2\2\u0370\u037b\bI\1\2\u0371\u0372\7 \2"+
		"\2\u0372\u037b\bI\1\2\u0373\u0374\7A\2\2\u0374\u037b\bI\1\2\u0375\u0376"+
		"\7\5\2\2\u0376\u0377\5\u008cG\2\u0377\u0378\7\6\2\2\u0378\u0379\bI\1\2"+
		"\u0379\u037b\3\2\2\2\u037a\u036d\3\2\2\2\u037a\u036f\3\2\2\2\u037a\u0371"+
		"\3\2\2\2\u037a\u0373\3\2\2\2\u037a\u0375\3\2\2\2\u037b\u0091\3\2\2\2\u037c"+
		"\u0386\bJ\1\2\u037d\u037e\5\u008cG\2\u037e\u037f\bJ\1\2\u037f\u0386\3"+
		"\2\2\2\u0380\u0381\5\u008cG\2\u0381\u0382\7\4\2\2\u0382\u0383\5\u0092"+
		"J\2\u0383\u0384\bJ\1\2\u0384\u0386\3\2\2\2\u0385\u037c\3\2\2\2\u0385\u037d"+
		"\3\2\2\2\u0385\u0380\3\2\2\2\u0386\u0093\3\2\2\2\u0387\u0388\7A\2\2\u0388"+
		"\u0389\7\n\2\2\u0389\u038a\5\u008cG\2\u038a\u038b\bK\1\2\u038b\u0095\3"+
		"\2\2\2\u038c\u0396\bL\1\2\u038d\u038e\5\u0094K\2\u038e\u038f\bL\1\2\u038f"+
		"\u0396\3\2\2\2\u0390\u0391\5\u0094K\2\u0391\u0392\7\4\2\2\u0392\u0393"+
		"\5\u0096L\2\u0393\u0394\bL\1\2\u0394\u0396\3\2\2\2\u0395\u038c\3\2\2\2"+
		"\u0395\u038d\3\2\2\2\u0395\u0390\3\2\2\2\u0396\u0097\3\2\2\2\u0397\u0398"+
		"\5l\67\2\u0398\u0399\7\n\2\2\u0399\u039a\5\u008cG\2\u039a\u039b\bM\1\2"+
		"\u039b\u0099\3\2\2\2\"\u0149\u0155\u016e\u0179\u0189\u0198\u01a9\u01b0"+
		"\u01b7\u01cc\u01d7\u01e7\u021b\u0226\u0236\u0246\u0266\u0295\u02a6\u02a8"+
		"\u02b9\u02bb\u02ca\u0320\u0330\u033a\u033c\u0350\u036b\u037a\u0385\u0395";
	public static final ATN _ATN =
		new ATNDeserializer().deserialize(_serializedATN.toCharArray());
	static {
		_decisionToDFA = new DFA[_ATN.getNumberOfDecisions()];
		for (int i = 0; i < _ATN.getNumberOfDecisions(); i++) {
			_decisionToDFA[i] = new DFA(_ATN.getDecisionState(i), i);
		}
	}
}