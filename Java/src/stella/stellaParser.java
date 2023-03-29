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
		Surrogate_id_SYMB_59=60, Surrogate_id_SYMB_60=61, COMMENT_antlr_builtin=62, 
		MULTICOMMENT_antlr_builtin=63, StellaIdent=64, ExtensionName=65, INTEGER=66, 
		WS=67, ErrorToken=68;
	public static final int
		RULE_start_ListStellaIdent = 0, RULE_start_Program = 1, RULE_start_LanguageDecl = 2, 
		RULE_start_Extension = 3, RULE_start_ListExtensionName = 4, RULE_start_ListExtension = 5, 
		RULE_start_Decl = 6, RULE_start_ListDecl = 7, RULE_start_LocalDecl = 8, 
		RULE_start_ListLocalDecl = 9, RULE_start_Annotation = 10, RULE_start_ListAnnotation = 11, 
		RULE_start_ParamDecl = 12, RULE_start_ListParamDecl = 13, RULE_start_ReturnType = 14, 
		RULE_start_ThrowType = 15, RULE_start_Expr = 16, RULE_start_ListExpr = 17, 
		RULE_start_MatchCase = 18, RULE_start_ListMatchCase = 19, RULE_start_OptionalTyping = 20, 
		RULE_start_PatternData = 21, RULE_start_ExprData = 22, RULE_start_Pattern = 23, 
		RULE_start_ListPattern = 24, RULE_start_LabelledPattern = 25, RULE_start_ListLabelledPattern = 26, 
		RULE_start_Binding = 27, RULE_start_ListBinding = 28, RULE_start_Expr1 = 29, 
		RULE_start_Expr2 = 30, RULE_start_Expr3 = 31, RULE_start_Expr4 = 32, RULE_start_Expr5 = 33, 
		RULE_start_Expr6 = 34, RULE_start_Type = 35, RULE_start_Type1 = 36, RULE_start_Type2 = 37, 
		RULE_start_Type3 = 38, RULE_start_ListType = 39, RULE_start_VariantFieldType = 40, 
		RULE_start_ListVariantFieldType = 41, RULE_start_RecordFieldType = 42, 
		RULE_start_ListRecordFieldType = 43, RULE_start_Typing = 44, RULE_listStellaIdent = 45, 
		RULE_program = 46, RULE_languageDecl = 47, RULE_extension = 48, RULE_listExtensionName = 49, 
		RULE_listExtension = 50, RULE_decl = 51, RULE_listDecl = 52, RULE_localDecl = 53, 
		RULE_listLocalDecl = 54, RULE_annotation = 55, RULE_listAnnotation = 56, 
		RULE_paramDecl = 57, RULE_listParamDecl = 58, RULE_returnType = 59, RULE_throwType = 60, 
		RULE_expr = 61, RULE_listExpr = 62, RULE_matchCase = 63, RULE_listMatchCase = 64, 
		RULE_optionalTyping = 65, RULE_patternData = 66, RULE_exprData = 67, RULE_pattern = 68, 
		RULE_listPattern = 69, RULE_labelledPattern = 70, RULE_listLabelledPattern = 71, 
		RULE_binding = 72, RULE_listBinding = 73, RULE_expr1 = 74, RULE_expr2 = 75, 
		RULE_expr3 = 76, RULE_expr4 = 77, RULE_expr5 = 78, RULE_expr6 = 79, RULE_type = 80, 
		RULE_type1 = 81, RULE_type2 = 82, RULE_type3 = 83, RULE_listType = 84, 
		RULE_variantFieldType = 85, RULE_listVariantFieldType = 86, RULE_recordFieldType = 87, 
		RULE_listRecordFieldType = 88, RULE_typing = 89;
	private static String[] makeRuleNames() {
		return new String[] {
			"start_ListStellaIdent", "start_Program", "start_LanguageDecl", "start_Extension", 
			"start_ListExtensionName", "start_ListExtension", "start_Decl", "start_ListDecl", 
			"start_LocalDecl", "start_ListLocalDecl", "start_Annotation", "start_ListAnnotation", 
			"start_ParamDecl", "start_ListParamDecl", "start_ReturnType", "start_ThrowType", 
			"start_Expr", "start_ListExpr", "start_MatchCase", "start_ListMatchCase", 
			"start_OptionalTyping", "start_PatternData", "start_ExprData", "start_Pattern", 
			"start_ListPattern", "start_LabelledPattern", "start_ListLabelledPattern", 
			"start_Binding", "start_ListBinding", "start_Expr1", "start_Expr2", "start_Expr3", 
			"start_Expr4", "start_Expr5", "start_Expr6", "start_Type", "start_Type1", 
			"start_Type2", "start_Type3", "start_ListType", "start_VariantFieldType", 
			"start_ListVariantFieldType", "start_RecordFieldType", "start_ListRecordFieldType", 
			"start_Typing", "listStellaIdent", "program", "languageDecl", "extension", 
			"listExtensionName", "listExtension", "decl", "listDecl", "localDecl", 
			"listLocalDecl", "annotation", "listAnnotation", "paramDecl", "listParamDecl", 
			"returnType", "throwType", "expr", "listExpr", "matchCase", "listMatchCase", 
			"optionalTyping", "patternData", "exprData", "pattern", "listPattern", 
			"labelledPattern", "listLabelledPattern", "binding", "listBinding", "expr1", 
			"expr2", "expr3", "expr4", "expr5", "expr6", "type", "type1", "type2", 
			"type3", "listType", "variantFieldType", "listVariantFieldType", "recordFieldType", 
			"listRecordFieldType", "typing"
		};
	}
	public static final String[] ruleNames = makeRuleNames();

	private static String[] makeLiteralNames() {
		return new String[] {
			null, "','", "';'", "'('", "')'", "'{'", "'}'", "'='", "':'", "'->'", 
			"'=>'", "'<|'", "'|>'", "'['", "']'", "'<'", "'<='", "'>'", "'>='", "'=='", 
			"'!='", "'+'", "'*'", "'List::head'", "'List::isempty'", "'List::tail'", 
			"'Nat::pred'", "'Nat::iszero'", "'Nat::rec'", "'.'", "'Bool'", "'Nat'", 
			"'Unit'", "'and'", "'as'", "'cons'", "'core'", "'else'", "'extend'", 
			"'false'", "'fix'", "'fn'", "'fold'", "'if'", "'in'", "'inline'", "'language'", 
			"'let'", "'match'", "'not'", "'or'", "'record'", "'return'", "'succ'", 
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
			"Surrogate_id_SYMB_60", "COMMENT_antlr_builtin", "MULTICOMMENT_antlr_builtin", 
			"StellaIdent", "ExtensionName", "INTEGER", "WS", "ErrorToken"
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

	public static class Start_ListStellaIdentContext extends ParserRuleContext {
		public stella.Absyn.ListStellaIdent result;
		public ListStellaIdentContext x;
		public TerminalNode EOF() { return getToken(stellaParser.EOF, 0); }
		public ListStellaIdentContext listStellaIdent() {
			return getRuleContext(ListStellaIdentContext.class,0);
		}
		public Start_ListStellaIdentContext(ParserRuleContext parent, int invokingState) {
			super(parent, invokingState);
		}
		@Override public int getRuleIndex() { return RULE_start_ListStellaIdent; }
		@Override
		public void enterRule(ParseTreeListener listener) {
			if ( listener instanceof stellaParserListener ) ((stellaParserListener)listener).enterStart_ListStellaIdent(this);
		}
		@Override
		public void exitRule(ParseTreeListener listener) {
			if ( listener instanceof stellaParserListener ) ((stellaParserListener)listener).exitStart_ListStellaIdent(this);
		}
	}

	public final Start_ListStellaIdentContext start_ListStellaIdent() throws RecognitionException {
		Start_ListStellaIdentContext _localctx = new Start_ListStellaIdentContext(_ctx, getState());
		enterRule(_localctx, 0, RULE_start_ListStellaIdent);
		try {
			enterOuterAlt(_localctx, 1);
			{
			setState(180);
			((Start_ListStellaIdentContext)_localctx).x = listStellaIdent();
			setState(181);
			match(EOF);
			 ((Start_ListStellaIdentContext)_localctx).result =  ((Start_ListStellaIdentContext)_localctx).x.result; 
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
		enterRule(_localctx, 2, RULE_start_Program);
		try {
			enterOuterAlt(_localctx, 1);
			{
			setState(184);
			((Start_ProgramContext)_localctx).x = program();
			setState(185);
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
		enterRule(_localctx, 4, RULE_start_LanguageDecl);
		try {
			enterOuterAlt(_localctx, 1);
			{
			setState(188);
			((Start_LanguageDeclContext)_localctx).x = languageDecl();
			setState(189);
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
		enterRule(_localctx, 6, RULE_start_Extension);
		try {
			enterOuterAlt(_localctx, 1);
			{
			setState(192);
			((Start_ExtensionContext)_localctx).x = extension();
			setState(193);
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
		enterRule(_localctx, 8, RULE_start_ListExtensionName);
		try {
			enterOuterAlt(_localctx, 1);
			{
			setState(196);
			((Start_ListExtensionNameContext)_localctx).x = listExtensionName();
			setState(197);
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
		enterRule(_localctx, 10, RULE_start_ListExtension);
		try {
			enterOuterAlt(_localctx, 1);
			{
			setState(200);
			((Start_ListExtensionContext)_localctx).x = listExtension(0);
			setState(201);
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
		enterRule(_localctx, 12, RULE_start_Decl);
		try {
			enterOuterAlt(_localctx, 1);
			{
			setState(204);
			((Start_DeclContext)_localctx).x = decl();
			setState(205);
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
		enterRule(_localctx, 14, RULE_start_ListDecl);
		try {
			enterOuterAlt(_localctx, 1);
			{
			setState(208);
			((Start_ListDeclContext)_localctx).x = listDecl(0);
			setState(209);
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
		enterRule(_localctx, 16, RULE_start_LocalDecl);
		try {
			enterOuterAlt(_localctx, 1);
			{
			setState(212);
			((Start_LocalDeclContext)_localctx).x = localDecl();
			setState(213);
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
		enterRule(_localctx, 18, RULE_start_ListLocalDecl);
		try {
			enterOuterAlt(_localctx, 1);
			{
			setState(216);
			((Start_ListLocalDeclContext)_localctx).x = listLocalDecl(0);
			setState(217);
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
		enterRule(_localctx, 20, RULE_start_Annotation);
		try {
			enterOuterAlt(_localctx, 1);
			{
			setState(220);
			((Start_AnnotationContext)_localctx).x = annotation();
			setState(221);
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
		enterRule(_localctx, 22, RULE_start_ListAnnotation);
		try {
			enterOuterAlt(_localctx, 1);
			{
			setState(224);
			((Start_ListAnnotationContext)_localctx).x = listAnnotation(0);
			setState(225);
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
		enterRule(_localctx, 24, RULE_start_ParamDecl);
		try {
			enterOuterAlt(_localctx, 1);
			{
			setState(228);
			((Start_ParamDeclContext)_localctx).x = paramDecl();
			setState(229);
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
		enterRule(_localctx, 26, RULE_start_ListParamDecl);
		try {
			enterOuterAlt(_localctx, 1);
			{
			setState(232);
			((Start_ListParamDeclContext)_localctx).x = listParamDecl();
			setState(233);
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
		enterRule(_localctx, 28, RULE_start_ReturnType);
		try {
			enterOuterAlt(_localctx, 1);
			{
			setState(236);
			((Start_ReturnTypeContext)_localctx).x = returnType();
			setState(237);
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
		enterRule(_localctx, 30, RULE_start_ThrowType);
		try {
			enterOuterAlt(_localctx, 1);
			{
			setState(240);
			((Start_ThrowTypeContext)_localctx).x = throwType();
			setState(241);
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
		enterRule(_localctx, 32, RULE_start_Expr);
		try {
			enterOuterAlt(_localctx, 1);
			{
			setState(244);
			((Start_ExprContext)_localctx).x = expr();
			setState(245);
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
		enterRule(_localctx, 34, RULE_start_ListExpr);
		try {
			enterOuterAlt(_localctx, 1);
			{
			setState(248);
			((Start_ListExprContext)_localctx).x = listExpr();
			setState(249);
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
		enterRule(_localctx, 36, RULE_start_MatchCase);
		try {
			enterOuterAlt(_localctx, 1);
			{
			setState(252);
			((Start_MatchCaseContext)_localctx).x = matchCase();
			setState(253);
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
		enterRule(_localctx, 38, RULE_start_ListMatchCase);
		try {
			enterOuterAlt(_localctx, 1);
			{
			setState(256);
			((Start_ListMatchCaseContext)_localctx).x = listMatchCase();
			setState(257);
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

	public static class Start_OptionalTypingContext extends ParserRuleContext {
		public stella.Absyn.OptionalTyping result;
		public OptionalTypingContext x;
		public TerminalNode EOF() { return getToken(stellaParser.EOF, 0); }
		public OptionalTypingContext optionalTyping() {
			return getRuleContext(OptionalTypingContext.class,0);
		}
		public Start_OptionalTypingContext(ParserRuleContext parent, int invokingState) {
			super(parent, invokingState);
		}
		@Override public int getRuleIndex() { return RULE_start_OptionalTyping; }
		@Override
		public void enterRule(ParseTreeListener listener) {
			if ( listener instanceof stellaParserListener ) ((stellaParserListener)listener).enterStart_OptionalTyping(this);
		}
		@Override
		public void exitRule(ParseTreeListener listener) {
			if ( listener instanceof stellaParserListener ) ((stellaParserListener)listener).exitStart_OptionalTyping(this);
		}
	}

	public final Start_OptionalTypingContext start_OptionalTyping() throws RecognitionException {
		Start_OptionalTypingContext _localctx = new Start_OptionalTypingContext(_ctx, getState());
		enterRule(_localctx, 40, RULE_start_OptionalTyping);
		try {
			enterOuterAlt(_localctx, 1);
			{
			setState(260);
			((Start_OptionalTypingContext)_localctx).x = optionalTyping();
			setState(261);
			match(EOF);
			 ((Start_OptionalTypingContext)_localctx).result =  ((Start_OptionalTypingContext)_localctx).x.result; 
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

	public static class Start_PatternDataContext extends ParserRuleContext {
		public stella.Absyn.PatternData result;
		public PatternDataContext x;
		public TerminalNode EOF() { return getToken(stellaParser.EOF, 0); }
		public PatternDataContext patternData() {
			return getRuleContext(PatternDataContext.class,0);
		}
		public Start_PatternDataContext(ParserRuleContext parent, int invokingState) {
			super(parent, invokingState);
		}
		@Override public int getRuleIndex() { return RULE_start_PatternData; }
		@Override
		public void enterRule(ParseTreeListener listener) {
			if ( listener instanceof stellaParserListener ) ((stellaParserListener)listener).enterStart_PatternData(this);
		}
		@Override
		public void exitRule(ParseTreeListener listener) {
			if ( listener instanceof stellaParserListener ) ((stellaParserListener)listener).exitStart_PatternData(this);
		}
	}

	public final Start_PatternDataContext start_PatternData() throws RecognitionException {
		Start_PatternDataContext _localctx = new Start_PatternDataContext(_ctx, getState());
		enterRule(_localctx, 42, RULE_start_PatternData);
		try {
			enterOuterAlt(_localctx, 1);
			{
			setState(264);
			((Start_PatternDataContext)_localctx).x = patternData();
			setState(265);
			match(EOF);
			 ((Start_PatternDataContext)_localctx).result =  ((Start_PatternDataContext)_localctx).x.result; 
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

	public static class Start_ExprDataContext extends ParserRuleContext {
		public stella.Absyn.ExprData result;
		public ExprDataContext x;
		public TerminalNode EOF() { return getToken(stellaParser.EOF, 0); }
		public ExprDataContext exprData() {
			return getRuleContext(ExprDataContext.class,0);
		}
		public Start_ExprDataContext(ParserRuleContext parent, int invokingState) {
			super(parent, invokingState);
		}
		@Override public int getRuleIndex() { return RULE_start_ExprData; }
		@Override
		public void enterRule(ParseTreeListener listener) {
			if ( listener instanceof stellaParserListener ) ((stellaParserListener)listener).enterStart_ExprData(this);
		}
		@Override
		public void exitRule(ParseTreeListener listener) {
			if ( listener instanceof stellaParserListener ) ((stellaParserListener)listener).exitStart_ExprData(this);
		}
	}

	public final Start_ExprDataContext start_ExprData() throws RecognitionException {
		Start_ExprDataContext _localctx = new Start_ExprDataContext(_ctx, getState());
		enterRule(_localctx, 44, RULE_start_ExprData);
		try {
			enterOuterAlt(_localctx, 1);
			{
			setState(268);
			((Start_ExprDataContext)_localctx).x = exprData();
			setState(269);
			match(EOF);
			 ((Start_ExprDataContext)_localctx).result =  ((Start_ExprDataContext)_localctx).x.result; 
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
		enterRule(_localctx, 46, RULE_start_Pattern);
		try {
			enterOuterAlt(_localctx, 1);
			{
			setState(272);
			((Start_PatternContext)_localctx).x = pattern();
			setState(273);
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
		enterRule(_localctx, 48, RULE_start_ListPattern);
		try {
			enterOuterAlt(_localctx, 1);
			{
			setState(276);
			((Start_ListPatternContext)_localctx).x = listPattern();
			setState(277);
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
		enterRule(_localctx, 50, RULE_start_LabelledPattern);
		try {
			enterOuterAlt(_localctx, 1);
			{
			setState(280);
			((Start_LabelledPatternContext)_localctx).x = labelledPattern();
			setState(281);
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
		enterRule(_localctx, 52, RULE_start_ListLabelledPattern);
		try {
			enterOuterAlt(_localctx, 1);
			{
			setState(284);
			((Start_ListLabelledPatternContext)_localctx).x = listLabelledPattern();
			setState(285);
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
		enterRule(_localctx, 54, RULE_start_Binding);
		try {
			enterOuterAlt(_localctx, 1);
			{
			setState(288);
			((Start_BindingContext)_localctx).x = binding();
			setState(289);
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
		enterRule(_localctx, 56, RULE_start_ListBinding);
		try {
			enterOuterAlt(_localctx, 1);
			{
			setState(292);
			((Start_ListBindingContext)_localctx).x = listBinding();
			setState(293);
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
		enterRule(_localctx, 58, RULE_start_Expr1);
		try {
			enterOuterAlt(_localctx, 1);
			{
			setState(296);
			((Start_Expr1Context)_localctx).x = expr1();
			setState(297);
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
		enterRule(_localctx, 60, RULE_start_Expr2);
		try {
			enterOuterAlt(_localctx, 1);
			{
			setState(300);
			((Start_Expr2Context)_localctx).x = expr2(0);
			setState(301);
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
		enterRule(_localctx, 62, RULE_start_Expr3);
		try {
			enterOuterAlt(_localctx, 1);
			{
			setState(304);
			((Start_Expr3Context)_localctx).x = expr3(0);
			setState(305);
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
		enterRule(_localctx, 64, RULE_start_Expr4);
		try {
			enterOuterAlt(_localctx, 1);
			{
			setState(308);
			((Start_Expr4Context)_localctx).x = expr4(0);
			setState(309);
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
		enterRule(_localctx, 66, RULE_start_Expr5);
		try {
			enterOuterAlt(_localctx, 1);
			{
			setState(312);
			((Start_Expr5Context)_localctx).x = expr5();
			setState(313);
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

	public static class Start_Expr6Context extends ParserRuleContext {
		public stella.Absyn.Expr result;
		public Expr6Context x;
		public TerminalNode EOF() { return getToken(stellaParser.EOF, 0); }
		public Expr6Context expr6() {
			return getRuleContext(Expr6Context.class,0);
		}
		public Start_Expr6Context(ParserRuleContext parent, int invokingState) {
			super(parent, invokingState);
		}
		@Override public int getRuleIndex() { return RULE_start_Expr6; }
		@Override
		public void enterRule(ParseTreeListener listener) {
			if ( listener instanceof stellaParserListener ) ((stellaParserListener)listener).enterStart_Expr6(this);
		}
		@Override
		public void exitRule(ParseTreeListener listener) {
			if ( listener instanceof stellaParserListener ) ((stellaParserListener)listener).exitStart_Expr6(this);
		}
	}

	public final Start_Expr6Context start_Expr6() throws RecognitionException {
		Start_Expr6Context _localctx = new Start_Expr6Context(_ctx, getState());
		enterRule(_localctx, 68, RULE_start_Expr6);
		try {
			enterOuterAlt(_localctx, 1);
			{
			setState(316);
			((Start_Expr6Context)_localctx).x = expr6(0);
			setState(317);
			match(EOF);
			 ((Start_Expr6Context)_localctx).result =  ((Start_Expr6Context)_localctx).x.result; 
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
		enterRule(_localctx, 70, RULE_start_Type);
		try {
			enterOuterAlt(_localctx, 1);
			{
			setState(320);
			((Start_TypeContext)_localctx).x = type();
			setState(321);
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
		enterRule(_localctx, 72, RULE_start_Type1);
		try {
			enterOuterAlt(_localctx, 1);
			{
			setState(324);
			((Start_Type1Context)_localctx).x = type1();
			setState(325);
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
		enterRule(_localctx, 74, RULE_start_Type2);
		try {
			enterOuterAlt(_localctx, 1);
			{
			setState(328);
			((Start_Type2Context)_localctx).x = type2();
			setState(329);
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

	public static class Start_Type3Context extends ParserRuleContext {
		public stella.Absyn.Type result;
		public Type3Context x;
		public TerminalNode EOF() { return getToken(stellaParser.EOF, 0); }
		public Type3Context type3() {
			return getRuleContext(Type3Context.class,0);
		}
		public Start_Type3Context(ParserRuleContext parent, int invokingState) {
			super(parent, invokingState);
		}
		@Override public int getRuleIndex() { return RULE_start_Type3; }
		@Override
		public void enterRule(ParseTreeListener listener) {
			if ( listener instanceof stellaParserListener ) ((stellaParserListener)listener).enterStart_Type3(this);
		}
		@Override
		public void exitRule(ParseTreeListener listener) {
			if ( listener instanceof stellaParserListener ) ((stellaParserListener)listener).exitStart_Type3(this);
		}
	}

	public final Start_Type3Context start_Type3() throws RecognitionException {
		Start_Type3Context _localctx = new Start_Type3Context(_ctx, getState());
		enterRule(_localctx, 76, RULE_start_Type3);
		try {
			enterOuterAlt(_localctx, 1);
			{
			setState(332);
			((Start_Type3Context)_localctx).x = type3();
			setState(333);
			match(EOF);
			 ((Start_Type3Context)_localctx).result =  ((Start_Type3Context)_localctx).x.result; 
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
		enterRule(_localctx, 78, RULE_start_ListType);
		try {
			enterOuterAlt(_localctx, 1);
			{
			setState(336);
			((Start_ListTypeContext)_localctx).x = listType();
			setState(337);
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

	public static class Start_VariantFieldTypeContext extends ParserRuleContext {
		public stella.Absyn.VariantFieldType result;
		public VariantFieldTypeContext x;
		public TerminalNode EOF() { return getToken(stellaParser.EOF, 0); }
		public VariantFieldTypeContext variantFieldType() {
			return getRuleContext(VariantFieldTypeContext.class,0);
		}
		public Start_VariantFieldTypeContext(ParserRuleContext parent, int invokingState) {
			super(parent, invokingState);
		}
		@Override public int getRuleIndex() { return RULE_start_VariantFieldType; }
		@Override
		public void enterRule(ParseTreeListener listener) {
			if ( listener instanceof stellaParserListener ) ((stellaParserListener)listener).enterStart_VariantFieldType(this);
		}
		@Override
		public void exitRule(ParseTreeListener listener) {
			if ( listener instanceof stellaParserListener ) ((stellaParserListener)listener).exitStart_VariantFieldType(this);
		}
	}

	public final Start_VariantFieldTypeContext start_VariantFieldType() throws RecognitionException {
		Start_VariantFieldTypeContext _localctx = new Start_VariantFieldTypeContext(_ctx, getState());
		enterRule(_localctx, 80, RULE_start_VariantFieldType);
		try {
			enterOuterAlt(_localctx, 1);
			{
			setState(340);
			((Start_VariantFieldTypeContext)_localctx).x = variantFieldType();
			setState(341);
			match(EOF);
			 ((Start_VariantFieldTypeContext)_localctx).result =  ((Start_VariantFieldTypeContext)_localctx).x.result; 
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

	public static class Start_ListVariantFieldTypeContext extends ParserRuleContext {
		public stella.Absyn.ListVariantFieldType result;
		public ListVariantFieldTypeContext x;
		public TerminalNode EOF() { return getToken(stellaParser.EOF, 0); }
		public ListVariantFieldTypeContext listVariantFieldType() {
			return getRuleContext(ListVariantFieldTypeContext.class,0);
		}
		public Start_ListVariantFieldTypeContext(ParserRuleContext parent, int invokingState) {
			super(parent, invokingState);
		}
		@Override public int getRuleIndex() { return RULE_start_ListVariantFieldType; }
		@Override
		public void enterRule(ParseTreeListener listener) {
			if ( listener instanceof stellaParserListener ) ((stellaParserListener)listener).enterStart_ListVariantFieldType(this);
		}
		@Override
		public void exitRule(ParseTreeListener listener) {
			if ( listener instanceof stellaParserListener ) ((stellaParserListener)listener).exitStart_ListVariantFieldType(this);
		}
	}

	public final Start_ListVariantFieldTypeContext start_ListVariantFieldType() throws RecognitionException {
		Start_ListVariantFieldTypeContext _localctx = new Start_ListVariantFieldTypeContext(_ctx, getState());
		enterRule(_localctx, 82, RULE_start_ListVariantFieldType);
		try {
			enterOuterAlt(_localctx, 1);
			{
			setState(344);
			((Start_ListVariantFieldTypeContext)_localctx).x = listVariantFieldType();
			setState(345);
			match(EOF);
			 ((Start_ListVariantFieldTypeContext)_localctx).result =  ((Start_ListVariantFieldTypeContext)_localctx).x.result; 
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

	public static class Start_RecordFieldTypeContext extends ParserRuleContext {
		public stella.Absyn.RecordFieldType result;
		public RecordFieldTypeContext x;
		public TerminalNode EOF() { return getToken(stellaParser.EOF, 0); }
		public RecordFieldTypeContext recordFieldType() {
			return getRuleContext(RecordFieldTypeContext.class,0);
		}
		public Start_RecordFieldTypeContext(ParserRuleContext parent, int invokingState) {
			super(parent, invokingState);
		}
		@Override public int getRuleIndex() { return RULE_start_RecordFieldType; }
		@Override
		public void enterRule(ParseTreeListener listener) {
			if ( listener instanceof stellaParserListener ) ((stellaParserListener)listener).enterStart_RecordFieldType(this);
		}
		@Override
		public void exitRule(ParseTreeListener listener) {
			if ( listener instanceof stellaParserListener ) ((stellaParserListener)listener).exitStart_RecordFieldType(this);
		}
	}

	public final Start_RecordFieldTypeContext start_RecordFieldType() throws RecognitionException {
		Start_RecordFieldTypeContext _localctx = new Start_RecordFieldTypeContext(_ctx, getState());
		enterRule(_localctx, 84, RULE_start_RecordFieldType);
		try {
			enterOuterAlt(_localctx, 1);
			{
			setState(348);
			((Start_RecordFieldTypeContext)_localctx).x = recordFieldType();
			setState(349);
			match(EOF);
			 ((Start_RecordFieldTypeContext)_localctx).result =  ((Start_RecordFieldTypeContext)_localctx).x.result; 
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

	public static class Start_ListRecordFieldTypeContext extends ParserRuleContext {
		public stella.Absyn.ListRecordFieldType result;
		public ListRecordFieldTypeContext x;
		public TerminalNode EOF() { return getToken(stellaParser.EOF, 0); }
		public ListRecordFieldTypeContext listRecordFieldType() {
			return getRuleContext(ListRecordFieldTypeContext.class,0);
		}
		public Start_ListRecordFieldTypeContext(ParserRuleContext parent, int invokingState) {
			super(parent, invokingState);
		}
		@Override public int getRuleIndex() { return RULE_start_ListRecordFieldType; }
		@Override
		public void enterRule(ParseTreeListener listener) {
			if ( listener instanceof stellaParserListener ) ((stellaParserListener)listener).enterStart_ListRecordFieldType(this);
		}
		@Override
		public void exitRule(ParseTreeListener listener) {
			if ( listener instanceof stellaParserListener ) ((stellaParserListener)listener).exitStart_ListRecordFieldType(this);
		}
	}

	public final Start_ListRecordFieldTypeContext start_ListRecordFieldType() throws RecognitionException {
		Start_ListRecordFieldTypeContext _localctx = new Start_ListRecordFieldTypeContext(_ctx, getState());
		enterRule(_localctx, 86, RULE_start_ListRecordFieldType);
		try {
			enterOuterAlt(_localctx, 1);
			{
			setState(352);
			((Start_ListRecordFieldTypeContext)_localctx).x = listRecordFieldType();
			setState(353);
			match(EOF);
			 ((Start_ListRecordFieldTypeContext)_localctx).result =  ((Start_ListRecordFieldTypeContext)_localctx).x.result; 
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
		enterRule(_localctx, 88, RULE_start_Typing);
		try {
			enterOuterAlt(_localctx, 1);
			{
			setState(356);
			((Start_TypingContext)_localctx).x = typing();
			setState(357);
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

	public static class ListStellaIdentContext extends ParserRuleContext {
		public stella.Absyn.ListStellaIdent result;
		public Token p_2_1;
		public Token p_3_1;
		public ListStellaIdentContext p_3_3;
		public TerminalNode StellaIdent() { return getToken(stellaParser.StellaIdent, 0); }
		public TerminalNode Surrogate_id_SYMB_0() { return getToken(stellaParser.Surrogate_id_SYMB_0, 0); }
		public ListStellaIdentContext listStellaIdent() {
			return getRuleContext(ListStellaIdentContext.class,0);
		}
		public ListStellaIdentContext(ParserRuleContext parent, int invokingState) {
			super(parent, invokingState);
		}
		@Override public int getRuleIndex() { return RULE_listStellaIdent; }
		@Override
		public void enterRule(ParseTreeListener listener) {
			if ( listener instanceof stellaParserListener ) ((stellaParserListener)listener).enterListStellaIdent(this);
		}
		@Override
		public void exitRule(ParseTreeListener listener) {
			if ( listener instanceof stellaParserListener ) ((stellaParserListener)listener).exitListStellaIdent(this);
		}
	}

	public final ListStellaIdentContext listStellaIdent() throws RecognitionException {
		ListStellaIdentContext _localctx = new ListStellaIdentContext(_ctx, getState());
		enterRule(_localctx, 90, RULE_listStellaIdent);
		try {
			setState(368);
			_errHandler.sync(this);
			switch ( getInterpreter().adaptivePredict(_input,0,_ctx) ) {
			case 1:
				enterOuterAlt(_localctx, 1);
				{
				 ((ListStellaIdentContext)_localctx).result =  new stella.Absyn.ListStellaIdent(); 
				}
				break;
			case 2:
				enterOuterAlt(_localctx, 2);
				{
				setState(361);
				((ListStellaIdentContext)_localctx).p_2_1 = match(StellaIdent);
				 ((ListStellaIdentContext)_localctx).result =  new stella.Absyn.ListStellaIdent(); _localctx.result.addLast(((ListStellaIdentContext)_localctx).p_2_1.getText()); 
				}
				break;
			case 3:
				enterOuterAlt(_localctx, 3);
				{
				setState(363);
				((ListStellaIdentContext)_localctx).p_3_1 = match(StellaIdent);
				setState(364);
				match(Surrogate_id_SYMB_0);
				setState(365);
				((ListStellaIdentContext)_localctx).p_3_3 = listStellaIdent();
				 ((ListStellaIdentContext)_localctx).result =  ((ListStellaIdentContext)_localctx).p_3_3.result; _localctx.result.addFirst(((ListStellaIdentContext)_localctx).p_3_1.getText()); 
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
		enterRule(_localctx, 92, RULE_program);
		try {
			enterOuterAlt(_localctx, 1);
			{
			setState(370);
			((ProgramContext)_localctx).p_1_1 = languageDecl();
			setState(371);
			((ProgramContext)_localctx).p_1_2 = listExtension(0);
			setState(372);
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
		public TerminalNode Surrogate_id_SYMB_45() { return getToken(stellaParser.Surrogate_id_SYMB_45, 0); }
		public TerminalNode Surrogate_id_SYMB_35() { return getToken(stellaParser.Surrogate_id_SYMB_35, 0); }
		public TerminalNode Surrogate_id_SYMB_1() { return getToken(stellaParser.Surrogate_id_SYMB_1, 0); }
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
		enterRule(_localctx, 94, RULE_languageDecl);
		try {
			enterOuterAlt(_localctx, 1);
			{
			setState(375);
			match(Surrogate_id_SYMB_45);
			setState(376);
			match(Surrogate_id_SYMB_35);
			setState(377);
			match(Surrogate_id_SYMB_1);
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
		public TerminalNode Surrogate_id_SYMB_37() { return getToken(stellaParser.Surrogate_id_SYMB_37, 0); }
		public TerminalNode Surrogate_id_SYMB_59() { return getToken(stellaParser.Surrogate_id_SYMB_59, 0); }
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
		enterRule(_localctx, 96, RULE_extension);
		try {
			enterOuterAlt(_localctx, 1);
			{
			setState(380);
			match(Surrogate_id_SYMB_37);
			setState(381);
			match(Surrogate_id_SYMB_59);
			setState(382);
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
		public TerminalNode Surrogate_id_SYMB_0() { return getToken(stellaParser.Surrogate_id_SYMB_0, 0); }
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
		enterRule(_localctx, 98, RULE_listExtensionName);
		try {
			setState(393);
			_errHandler.sync(this);
			switch ( getInterpreter().adaptivePredict(_input,1,_ctx) ) {
			case 1:
				enterOuterAlt(_localctx, 1);
				{
				 ((ListExtensionNameContext)_localctx).result =  new stella.Absyn.ListExtensionName(); 
				}
				break;
			case 2:
				enterOuterAlt(_localctx, 2);
				{
				setState(386);
				((ListExtensionNameContext)_localctx).p_2_1 = match(ExtensionName);
				 ((ListExtensionNameContext)_localctx).result =  new stella.Absyn.ListExtensionName(); _localctx.result.addLast(((ListExtensionNameContext)_localctx).p_2_1.getText()); 
				}
				break;
			case 3:
				enterOuterAlt(_localctx, 3);
				{
				setState(388);
				((ListExtensionNameContext)_localctx).p_3_1 = match(ExtensionName);
				setState(389);
				match(Surrogate_id_SYMB_0);
				setState(390);
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
		public TerminalNode Surrogate_id_SYMB_1() { return getToken(stellaParser.Surrogate_id_SYMB_1, 0); }
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
		int _startState = 100;
		enterRecursionRule(_localctx, 100, RULE_listExtension, _p);
		try {
			int _alt;
			enterOuterAlt(_localctx, 1);
			{
			{
			 ((ListExtensionContext)_localctx).result =  new stella.Absyn.ListExtension(); 
			}
			_ctx.stop = _input.LT(-1);
			setState(405);
			_errHandler.sync(this);
			_alt = getInterpreter().adaptivePredict(_input,2,_ctx);
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
					setState(398);
					if (!(precpred(_ctx, 1))) throw new FailedPredicateException(this, "precpred(_ctx, 1)");
					setState(399);
					((ListExtensionContext)_localctx).p_2_2 = extension();
					setState(400);
					match(Surrogate_id_SYMB_1);
					 ((ListExtensionContext)_localctx).result =  ((ListExtensionContext)_localctx).p_2_1.result; _localctx.result.addLast(((ListExtensionContext)_localctx).p_2_2.result); 
					}
					} 
				}
				setState(407);
				_errHandler.sync(this);
				_alt = getInterpreter().adaptivePredict(_input,2,_ctx);
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
		public TerminalNode Surrogate_id_SYMB_40() { return getToken(stellaParser.Surrogate_id_SYMB_40, 0); }
		public TerminalNode Surrogate_id_SYMB_2() { return getToken(stellaParser.Surrogate_id_SYMB_2, 0); }
		public TerminalNode Surrogate_id_SYMB_3() { return getToken(stellaParser.Surrogate_id_SYMB_3, 0); }
		public TerminalNode Surrogate_id_SYMB_4() { return getToken(stellaParser.Surrogate_id_SYMB_4, 0); }
		public TerminalNode Surrogate_id_SYMB_51() { return getToken(stellaParser.Surrogate_id_SYMB_51, 0); }
		public TerminalNode Surrogate_id_SYMB_1() { return getToken(stellaParser.Surrogate_id_SYMB_1, 0); }
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
		public TerminalNode Surrogate_id_SYMB_56() { return getToken(stellaParser.Surrogate_id_SYMB_56, 0); }
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
		enterRule(_localctx, 102, RULE_decl);
		try {
			setState(430);
			_errHandler.sync(this);
			switch ( getInterpreter().adaptivePredict(_input,3,_ctx) ) {
			case 1:
				enterOuterAlt(_localctx, 1);
				{
				setState(408);
				((DeclContext)_localctx).p_1_1 = listAnnotation(0);
				setState(409);
				match(Surrogate_id_SYMB_40);
				setState(410);
				((DeclContext)_localctx).p_1_3 = match(StellaIdent);
				setState(411);
				match(Surrogate_id_SYMB_2);
				setState(412);
				((DeclContext)_localctx).p_1_5 = listParamDecl();
				setState(413);
				match(Surrogate_id_SYMB_3);
				setState(414);
				((DeclContext)_localctx).p_1_7 = returnType();
				setState(415);
				((DeclContext)_localctx).p_1_8 = throwType();
				setState(416);
				match(Surrogate_id_SYMB_4);
				setState(417);
				((DeclContext)_localctx).p_1_10 = listDecl(0);
				setState(418);
				match(Surrogate_id_SYMB_51);
				setState(419);
				((DeclContext)_localctx).p_1_12 = expr();
				setState(420);
				match(Surrogate_id_SYMB_1);
				setState(421);
				match(Surrogate_id_SYMB_5);
				 ((DeclContext)_localctx).result =  new stella.Absyn.DeclFun(((DeclContext)_localctx).p_1_1.result,((DeclContext)_localctx).p_1_3.getText(),((DeclContext)_localctx).p_1_5.result,((DeclContext)_localctx).p_1_7.result,((DeclContext)_localctx).p_1_8.result,((DeclContext)_localctx).p_1_10.result,((DeclContext)_localctx).p_1_12.result); 
				}
				break;
			case 2:
				enterOuterAlt(_localctx, 2);
				{
				setState(424);
				match(Surrogate_id_SYMB_56);
				setState(425);
				((DeclContext)_localctx).p_2_2 = match(StellaIdent);
				setState(426);
				match(Surrogate_id_SYMB_6);
				setState(427);
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
		int _startState = 104;
		enterRecursionRule(_localctx, 104, RULE_listDecl, _p);
		try {
			int _alt;
			enterOuterAlt(_localctx, 1);
			{
			{
			 ((ListDeclContext)_localctx).result =  new stella.Absyn.ListDecl(); 
			}
			_ctx.stop = _input.LT(-1);
			setState(441);
			_errHandler.sync(this);
			_alt = getInterpreter().adaptivePredict(_input,4,_ctx);
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
					setState(435);
					if (!(precpred(_ctx, 1))) throw new FailedPredicateException(this, "precpred(_ctx, 1)");
					setState(436);
					((ListDeclContext)_localctx).p_2_2 = decl();
					 ((ListDeclContext)_localctx).result =  ((ListDeclContext)_localctx).p_2_1.result; _localctx.result.addLast(((ListDeclContext)_localctx).p_2_2.result); 
					}
					} 
				}
				setState(443);
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
		enterRule(_localctx, 106, RULE_localDecl);
		try {
			enterOuterAlt(_localctx, 1);
			{
			setState(444);
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
		public TerminalNode Surrogate_id_SYMB_1() { return getToken(stellaParser.Surrogate_id_SYMB_1, 0); }
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
		int _startState = 108;
		enterRecursionRule(_localctx, 108, RULE_listLocalDecl, _p);
		try {
			int _alt;
			enterOuterAlt(_localctx, 1);
			{
			{
			 ((ListLocalDeclContext)_localctx).result =  new stella.Absyn.ListLocalDecl(); 
			}
			_ctx.stop = _input.LT(-1);
			setState(457);
			_errHandler.sync(this);
			_alt = getInterpreter().adaptivePredict(_input,5,_ctx);
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
					setState(450);
					if (!(precpred(_ctx, 1))) throw new FailedPredicateException(this, "precpred(_ctx, 1)");
					setState(451);
					((ListLocalDeclContext)_localctx).p_2_2 = localDecl();
					setState(452);
					match(Surrogate_id_SYMB_1);
					 ((ListLocalDeclContext)_localctx).result =  ((ListLocalDeclContext)_localctx).p_2_1.result; _localctx.result.addLast(((ListLocalDeclContext)_localctx).p_2_2.result); 
					}
					} 
				}
				setState(459);
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

	public static class AnnotationContext extends ParserRuleContext {
		public stella.Absyn.Annotation result;
		public TerminalNode Surrogate_id_SYMB_44() { return getToken(stellaParser.Surrogate_id_SYMB_44, 0); }
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
		enterRule(_localctx, 110, RULE_annotation);
		try {
			enterOuterAlt(_localctx, 1);
			{
			setState(460);
			match(Surrogate_id_SYMB_44);
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
		int _startState = 112;
		enterRecursionRule(_localctx, 112, RULE_listAnnotation, _p);
		try {
			int _alt;
			enterOuterAlt(_localctx, 1);
			{
			{
			 ((ListAnnotationContext)_localctx).result =  new stella.Absyn.ListAnnotation(); 
			}
			_ctx.stop = _input.LT(-1);
			setState(472);
			_errHandler.sync(this);
			_alt = getInterpreter().adaptivePredict(_input,6,_ctx);
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
					setState(466);
					if (!(precpred(_ctx, 1))) throw new FailedPredicateException(this, "precpred(_ctx, 1)");
					setState(467);
					((ListAnnotationContext)_localctx).p_2_2 = annotation();
					 ((ListAnnotationContext)_localctx).result =  ((ListAnnotationContext)_localctx).p_2_1.result; _localctx.result.addLast(((ListAnnotationContext)_localctx).p_2_2.result); 
					}
					} 
				}
				setState(474);
				_errHandler.sync(this);
				_alt = getInterpreter().adaptivePredict(_input,6,_ctx);
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
		enterRule(_localctx, 114, RULE_paramDecl);
		try {
			enterOuterAlt(_localctx, 1);
			{
			setState(475);
			((ParamDeclContext)_localctx).p_1_1 = match(StellaIdent);
			setState(476);
			match(Surrogate_id_SYMB_7);
			setState(477);
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
		public TerminalNode Surrogate_id_SYMB_0() { return getToken(stellaParser.Surrogate_id_SYMB_0, 0); }
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
		enterRule(_localctx, 116, RULE_listParamDecl);
		try {
			setState(489);
			_errHandler.sync(this);
			switch ( getInterpreter().adaptivePredict(_input,7,_ctx) ) {
			case 1:
				enterOuterAlt(_localctx, 1);
				{
				 ((ListParamDeclContext)_localctx).result =  new stella.Absyn.ListParamDecl(); 
				}
				break;
			case 2:
				enterOuterAlt(_localctx, 2);
				{
				setState(481);
				((ListParamDeclContext)_localctx).p_2_1 = paramDecl();
				 ((ListParamDeclContext)_localctx).result =  new stella.Absyn.ListParamDecl(); _localctx.result.addLast(((ListParamDeclContext)_localctx).p_2_1.result); 
				}
				break;
			case 3:
				enterOuterAlt(_localctx, 3);
				{
				setState(484);
				((ListParamDeclContext)_localctx).p_3_1 = paramDecl();
				setState(485);
				match(Surrogate_id_SYMB_0);
				setState(486);
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
		enterRule(_localctx, 118, RULE_returnType);
		try {
			setState(496);
			_errHandler.sync(this);
			switch (_input.LA(1)) {
			case EOF:
			case Surrogate_id_SYMB_4:
			case Surrogate_id_SYMB_54:
				enterOuterAlt(_localctx, 1);
				{
				 ((ReturnTypeContext)_localctx).result =  new stella.Absyn.NoReturnType(); 
				}
				break;
			case Surrogate_id_SYMB_8:
				enterOuterAlt(_localctx, 2);
				{
				setState(492);
				match(Surrogate_id_SYMB_8);
				setState(493);
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
		public TerminalNode Surrogate_id_SYMB_54() { return getToken(stellaParser.Surrogate_id_SYMB_54, 0); }
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
		enterRule(_localctx, 120, RULE_throwType);
		try {
			setState(503);
			_errHandler.sync(this);
			switch (_input.LA(1)) {
			case EOF:
			case Surrogate_id_SYMB_4:
				enterOuterAlt(_localctx, 1);
				{
				 ((ThrowTypeContext)_localctx).result =  new stella.Absyn.NoThrowType(); 
				}
				break;
			case Surrogate_id_SYMB_54:
				enterOuterAlt(_localctx, 2);
				{
				setState(499);
				match(Surrogate_id_SYMB_54);
				setState(500);
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
		public TerminalNode Surrogate_id_SYMB_42() { return getToken(stellaParser.Surrogate_id_SYMB_42, 0); }
		public TerminalNode Surrogate_id_SYMB_53() { return getToken(stellaParser.Surrogate_id_SYMB_53, 0); }
		public TerminalNode Surrogate_id_SYMB_36() { return getToken(stellaParser.Surrogate_id_SYMB_36, 0); }
		public List<ExprContext> expr() {
			return getRuleContexts(ExprContext.class);
		}
		public ExprContext expr(int i) {
			return getRuleContext(ExprContext.class,i);
		}
		public TerminalNode Surrogate_id_SYMB_46() { return getToken(stellaParser.Surrogate_id_SYMB_46, 0); }
		public TerminalNode Surrogate_id_SYMB_6() { return getToken(stellaParser.Surrogate_id_SYMB_6, 0); }
		public TerminalNode Surrogate_id_SYMB_43() { return getToken(stellaParser.Surrogate_id_SYMB_43, 0); }
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
		enterRule(_localctx, 122, RULE_expr);
		try {
			setState(524);
			_errHandler.sync(this);
			switch (_input.LA(1)) {
			case Surrogate_id_SYMB_42:
				enterOuterAlt(_localctx, 1);
				{
				setState(505);
				match(Surrogate_id_SYMB_42);
				setState(506);
				((ExprContext)_localctx).p_1_2 = expr();
				setState(507);
				match(Surrogate_id_SYMB_53);
				setState(508);
				((ExprContext)_localctx).p_1_4 = expr();
				setState(509);
				match(Surrogate_id_SYMB_36);
				setState(510);
				((ExprContext)_localctx).p_1_6 = expr();
				 ((ExprContext)_localctx).result =  new stella.Absyn.If(((ExprContext)_localctx).p_1_2.result,((ExprContext)_localctx).p_1_4.result,((ExprContext)_localctx).p_1_6.result); 
				}
				break;
			case Surrogate_id_SYMB_46:
				enterOuterAlt(_localctx, 2);
				{
				setState(513);
				match(Surrogate_id_SYMB_46);
				setState(514);
				((ExprContext)_localctx).p_2_2 = match(StellaIdent);
				setState(515);
				match(Surrogate_id_SYMB_6);
				setState(516);
				((ExprContext)_localctx).p_2_4 = expr();
				setState(517);
				match(Surrogate_id_SYMB_43);
				setState(518);
				((ExprContext)_localctx).p_2_6 = expr();
				 ((ExprContext)_localctx).result =  new stella.Absyn.Let(((ExprContext)_localctx).p_2_2.getText(),((ExprContext)_localctx).p_2_4.result,((ExprContext)_localctx).p_2_6.result); 
				}
				break;
			case Surrogate_id_SYMB_2:
			case Surrogate_id_SYMB_4:
			case Surrogate_id_SYMB_10:
			case Surrogate_id_SYMB_12:
			case Surrogate_id_SYMB_22:
			case Surrogate_id_SYMB_23:
			case Surrogate_id_SYMB_24:
			case Surrogate_id_SYMB_25:
			case Surrogate_id_SYMB_26:
			case Surrogate_id_SYMB_27:
			case Surrogate_id_SYMB_34:
			case Surrogate_id_SYMB_38:
			case Surrogate_id_SYMB_39:
			case Surrogate_id_SYMB_40:
			case Surrogate_id_SYMB_41:
			case Surrogate_id_SYMB_47:
			case Surrogate_id_SYMB_48:
			case Surrogate_id_SYMB_50:
			case Surrogate_id_SYMB_52:
			case Surrogate_id_SYMB_55:
			case Surrogate_id_SYMB_57:
			case StellaIdent:
			case INTEGER:
				enterOuterAlt(_localctx, 3);
				{
				setState(521);
				((ExprContext)_localctx).p_3_1 = expr1();
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
		public TerminalNode Surrogate_id_SYMB_0() { return getToken(stellaParser.Surrogate_id_SYMB_0, 0); }
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
		enterRule(_localctx, 124, RULE_listExpr);
		try {
			setState(535);
			_errHandler.sync(this);
			switch ( getInterpreter().adaptivePredict(_input,11,_ctx) ) {
			case 1:
				enterOuterAlt(_localctx, 1);
				{
				 ((ListExprContext)_localctx).result =  new stella.Absyn.ListExpr(); 
				}
				break;
			case 2:
				enterOuterAlt(_localctx, 2);
				{
				setState(527);
				((ListExprContext)_localctx).p_2_1 = expr();
				 ((ListExprContext)_localctx).result =  new stella.Absyn.ListExpr(); _localctx.result.addLast(((ListExprContext)_localctx).p_2_1.result); 
				}
				break;
			case 3:
				enterOuterAlt(_localctx, 3);
				{
				setState(530);
				((ListExprContext)_localctx).p_3_1 = expr();
				setState(531);
				match(Surrogate_id_SYMB_0);
				setState(532);
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
		enterRule(_localctx, 126, RULE_matchCase);
		try {
			enterOuterAlt(_localctx, 1);
			{
			setState(537);
			((MatchCaseContext)_localctx).p_1_1 = pattern();
			setState(538);
			match(Surrogate_id_SYMB_9);
			setState(539);
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
		public TerminalNode Surrogate_id_SYMB_1() { return getToken(stellaParser.Surrogate_id_SYMB_1, 0); }
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
		enterRule(_localctx, 128, RULE_listMatchCase);
		try {
			setState(551);
			_errHandler.sync(this);
			switch ( getInterpreter().adaptivePredict(_input,12,_ctx) ) {
			case 1:
				enterOuterAlt(_localctx, 1);
				{
				 ((ListMatchCaseContext)_localctx).result =  new stella.Absyn.ListMatchCase(); 
				}
				break;
			case 2:
				enterOuterAlt(_localctx, 2);
				{
				setState(543);
				((ListMatchCaseContext)_localctx).p_2_1 = matchCase();
				 ((ListMatchCaseContext)_localctx).result =  new stella.Absyn.ListMatchCase(); _localctx.result.addLast(((ListMatchCaseContext)_localctx).p_2_1.result); 
				}
				break;
			case 3:
				enterOuterAlt(_localctx, 3);
				{
				setState(546);
				((ListMatchCaseContext)_localctx).p_3_1 = matchCase();
				setState(547);
				match(Surrogate_id_SYMB_1);
				setState(548);
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

	public static class OptionalTypingContext extends ParserRuleContext {
		public stella.Absyn.OptionalTyping result;
		public TypeContext p_2_2;
		public TerminalNode Surrogate_id_SYMB_7() { return getToken(stellaParser.Surrogate_id_SYMB_7, 0); }
		public TypeContext type() {
			return getRuleContext(TypeContext.class,0);
		}
		public OptionalTypingContext(ParserRuleContext parent, int invokingState) {
			super(parent, invokingState);
		}
		@Override public int getRuleIndex() { return RULE_optionalTyping; }
		@Override
		public void enterRule(ParseTreeListener listener) {
			if ( listener instanceof stellaParserListener ) ((stellaParserListener)listener).enterOptionalTyping(this);
		}
		@Override
		public void exitRule(ParseTreeListener listener) {
			if ( listener instanceof stellaParserListener ) ((stellaParserListener)listener).exitOptionalTyping(this);
		}
	}

	public final OptionalTypingContext optionalTyping() throws RecognitionException {
		OptionalTypingContext _localctx = new OptionalTypingContext(_ctx, getState());
		enterRule(_localctx, 130, RULE_optionalTyping);
		try {
			setState(558);
			_errHandler.sync(this);
			switch (_input.LA(1)) {
			case EOF:
			case Surrogate_id_SYMB_0:
			case Surrogate_id_SYMB_11:
				enterOuterAlt(_localctx, 1);
				{
				 ((OptionalTypingContext)_localctx).result =  new stella.Absyn.NoTyping(); 
				}
				break;
			case Surrogate_id_SYMB_7:
				enterOuterAlt(_localctx, 2);
				{
				setState(554);
				match(Surrogate_id_SYMB_7);
				setState(555);
				((OptionalTypingContext)_localctx).p_2_2 = type();
				 ((OptionalTypingContext)_localctx).result =  new stella.Absyn.SomeTyping(((OptionalTypingContext)_localctx).p_2_2.result); 
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

	public static class PatternDataContext extends ParserRuleContext {
		public stella.Absyn.PatternData result;
		public PatternContext p_2_2;
		public TerminalNode Surrogate_id_SYMB_6() { return getToken(stellaParser.Surrogate_id_SYMB_6, 0); }
		public PatternContext pattern() {
			return getRuleContext(PatternContext.class,0);
		}
		public PatternDataContext(ParserRuleContext parent, int invokingState) {
			super(parent, invokingState);
		}
		@Override public int getRuleIndex() { return RULE_patternData; }
		@Override
		public void enterRule(ParseTreeListener listener) {
			if ( listener instanceof stellaParserListener ) ((stellaParserListener)listener).enterPatternData(this);
		}
		@Override
		public void exitRule(ParseTreeListener listener) {
			if ( listener instanceof stellaParserListener ) ((stellaParserListener)listener).exitPatternData(this);
		}
	}

	public final PatternDataContext patternData() throws RecognitionException {
		PatternDataContext _localctx = new PatternDataContext(_ctx, getState());
		enterRule(_localctx, 132, RULE_patternData);
		try {
			setState(565);
			_errHandler.sync(this);
			switch (_input.LA(1)) {
			case EOF:
			case Surrogate_id_SYMB_11:
				enterOuterAlt(_localctx, 1);
				{
				 ((PatternDataContext)_localctx).result =  new stella.Absyn.NoPatternData(); 
				}
				break;
			case Surrogate_id_SYMB_6:
				enterOuterAlt(_localctx, 2);
				{
				setState(561);
				match(Surrogate_id_SYMB_6);
				setState(562);
				((PatternDataContext)_localctx).p_2_2 = pattern();
				 ((PatternDataContext)_localctx).result =  new stella.Absyn.SomePatternData(((PatternDataContext)_localctx).p_2_2.result); 
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

	public static class ExprDataContext extends ParserRuleContext {
		public stella.Absyn.ExprData result;
		public ExprContext p_2_2;
		public TerminalNode Surrogate_id_SYMB_6() { return getToken(stellaParser.Surrogate_id_SYMB_6, 0); }
		public ExprContext expr() {
			return getRuleContext(ExprContext.class,0);
		}
		public ExprDataContext(ParserRuleContext parent, int invokingState) {
			super(parent, invokingState);
		}
		@Override public int getRuleIndex() { return RULE_exprData; }
		@Override
		public void enterRule(ParseTreeListener listener) {
			if ( listener instanceof stellaParserListener ) ((stellaParserListener)listener).enterExprData(this);
		}
		@Override
		public void exitRule(ParseTreeListener listener) {
			if ( listener instanceof stellaParserListener ) ((stellaParserListener)listener).exitExprData(this);
		}
	}

	public final ExprDataContext exprData() throws RecognitionException {
		ExprDataContext _localctx = new ExprDataContext(_ctx, getState());
		enterRule(_localctx, 134, RULE_exprData);
		try {
			setState(572);
			_errHandler.sync(this);
			switch (_input.LA(1)) {
			case EOF:
			case Surrogate_id_SYMB_11:
				enterOuterAlt(_localctx, 1);
				{
				 ((ExprDataContext)_localctx).result =  new stella.Absyn.NoExprData(); 
				}
				break;
			case Surrogate_id_SYMB_6:
				enterOuterAlt(_localctx, 2);
				{
				setState(568);
				match(Surrogate_id_SYMB_6);
				setState(569);
				((ExprDataContext)_localctx).p_2_2 = expr();
				 ((ExprDataContext)_localctx).result =  new stella.Absyn.SomeExprData(((ExprDataContext)_localctx).p_2_2.result); 
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

	public static class PatternContext extends ParserRuleContext {
		public stella.Absyn.Pattern result;
		public Token p_1_2;
		public PatternDataContext p_1_3;
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
		public TerminalNode Surrogate_id_SYMB_11() { return getToken(stellaParser.Surrogate_id_SYMB_11, 0); }
		public TerminalNode StellaIdent() { return getToken(stellaParser.StellaIdent, 0); }
		public PatternDataContext patternData() {
			return getRuleContext(PatternDataContext.class,0);
		}
		public TerminalNode Surrogate_id_SYMB_4() { return getToken(stellaParser.Surrogate_id_SYMB_4, 0); }
		public TerminalNode Surrogate_id_SYMB_5() { return getToken(stellaParser.Surrogate_id_SYMB_5, 0); }
		public ListPatternContext listPattern() {
			return getRuleContext(ListPatternContext.class,0);
		}
		public TerminalNode Surrogate_id_SYMB_50() { return getToken(stellaParser.Surrogate_id_SYMB_50, 0); }
		public ListLabelledPatternContext listLabelledPattern() {
			return getRuleContext(ListLabelledPatternContext.class,0);
		}
		public TerminalNode Surrogate_id_SYMB_12() { return getToken(stellaParser.Surrogate_id_SYMB_12, 0); }
		public TerminalNode Surrogate_id_SYMB_13() { return getToken(stellaParser.Surrogate_id_SYMB_13, 0); }
		public TerminalNode Surrogate_id_SYMB_34() { return getToken(stellaParser.Surrogate_id_SYMB_34, 0); }
		public TerminalNode Surrogate_id_SYMB_2() { return getToken(stellaParser.Surrogate_id_SYMB_2, 0); }
		public TerminalNode Surrogate_id_SYMB_0() { return getToken(stellaParser.Surrogate_id_SYMB_0, 0); }
		public TerminalNode Surrogate_id_SYMB_3() { return getToken(stellaParser.Surrogate_id_SYMB_3, 0); }
		public List<PatternContext> pattern() {
			return getRuleContexts(PatternContext.class);
		}
		public PatternContext pattern(int i) {
			return getRuleContext(PatternContext.class,i);
		}
		public TerminalNode Surrogate_id_SYMB_38() { return getToken(stellaParser.Surrogate_id_SYMB_38, 0); }
		public TerminalNode Surrogate_id_SYMB_55() { return getToken(stellaParser.Surrogate_id_SYMB_55, 0); }
		public TerminalNode INTEGER() { return getToken(stellaParser.INTEGER, 0); }
		public TerminalNode Surrogate_id_SYMB_52() { return getToken(stellaParser.Surrogate_id_SYMB_52, 0); }
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
		enterRule(_localctx, 136, RULE_pattern);
		try {
			setState(623);
			_errHandler.sync(this);
			switch (_input.LA(1)) {
			case Surrogate_id_SYMB_10:
				enterOuterAlt(_localctx, 1);
				{
				setState(574);
				match(Surrogate_id_SYMB_10);
				setState(575);
				((PatternContext)_localctx).p_1_2 = match(StellaIdent);
				setState(576);
				((PatternContext)_localctx).p_1_3 = patternData();
				setState(577);
				match(Surrogate_id_SYMB_11);
				 ((PatternContext)_localctx).result =  new stella.Absyn.PatternVariant(((PatternContext)_localctx).p_1_2.getText(),((PatternContext)_localctx).p_1_3.result); 
				}
				break;
			case Surrogate_id_SYMB_4:
				enterOuterAlt(_localctx, 2);
				{
				setState(580);
				match(Surrogate_id_SYMB_4);
				setState(581);
				((PatternContext)_localctx).p_2_2 = listPattern();
				setState(582);
				match(Surrogate_id_SYMB_5);
				 ((PatternContext)_localctx).result =  new stella.Absyn.PatternTuple(((PatternContext)_localctx).p_2_2.result); 
				}
				break;
			case Surrogate_id_SYMB_50:
				enterOuterAlt(_localctx, 3);
				{
				setState(585);
				match(Surrogate_id_SYMB_50);
				setState(586);
				match(Surrogate_id_SYMB_4);
				setState(587);
				((PatternContext)_localctx).p_3_3 = listLabelledPattern();
				setState(588);
				match(Surrogate_id_SYMB_5);
				 ((PatternContext)_localctx).result =  new stella.Absyn.PatternRecord(((PatternContext)_localctx).p_3_3.result); 
				}
				break;
			case Surrogate_id_SYMB_12:
				enterOuterAlt(_localctx, 4);
				{
				setState(591);
				match(Surrogate_id_SYMB_12);
				setState(592);
				((PatternContext)_localctx).p_4_2 = listPattern();
				setState(593);
				match(Surrogate_id_SYMB_13);
				 ((PatternContext)_localctx).result =  new stella.Absyn.PatternList(((PatternContext)_localctx).p_4_2.result); 
				}
				break;
			case Surrogate_id_SYMB_34:
				enterOuterAlt(_localctx, 5);
				{
				setState(596);
				match(Surrogate_id_SYMB_34);
				setState(597);
				match(Surrogate_id_SYMB_2);
				setState(598);
				((PatternContext)_localctx).p_5_3 = pattern();
				setState(599);
				match(Surrogate_id_SYMB_0);
				setState(600);
				((PatternContext)_localctx).p_5_5 = pattern();
				setState(601);
				match(Surrogate_id_SYMB_3);
				 ((PatternContext)_localctx).result =  new stella.Absyn.PatternCons(((PatternContext)_localctx).p_5_3.result,((PatternContext)_localctx).p_5_5.result); 
				}
				break;
			case Surrogate_id_SYMB_38:
				enterOuterAlt(_localctx, 6);
				{
				setState(604);
				match(Surrogate_id_SYMB_38);
				 ((PatternContext)_localctx).result =  new stella.Absyn.PatternFalse(); 
				}
				break;
			case Surrogate_id_SYMB_55:
				enterOuterAlt(_localctx, 7);
				{
				setState(606);
				match(Surrogate_id_SYMB_55);
				 ((PatternContext)_localctx).result =  new stella.Absyn.PatternTrue(); 
				}
				break;
			case INTEGER:
				enterOuterAlt(_localctx, 8);
				{
				setState(608);
				((PatternContext)_localctx).p_8_1 = match(INTEGER);
				 ((PatternContext)_localctx).result =  new stella.Absyn.PatternInt(Integer.parseInt(((PatternContext)_localctx).p_8_1.getText())); 
				}
				break;
			case Surrogate_id_SYMB_52:
				enterOuterAlt(_localctx, 9);
				{
				setState(610);
				match(Surrogate_id_SYMB_52);
				setState(611);
				match(Surrogate_id_SYMB_2);
				setState(612);
				((PatternContext)_localctx).p_9_3 = pattern();
				setState(613);
				match(Surrogate_id_SYMB_3);
				 ((PatternContext)_localctx).result =  new stella.Absyn.PatternSucc(((PatternContext)_localctx).p_9_3.result); 
				}
				break;
			case StellaIdent:
				enterOuterAlt(_localctx, 10);
				{
				setState(616);
				((PatternContext)_localctx).p_10_1 = match(StellaIdent);
				 ((PatternContext)_localctx).result =  new stella.Absyn.PatternVar(((PatternContext)_localctx).p_10_1.getText()); 
				}
				break;
			case Surrogate_id_SYMB_2:
				enterOuterAlt(_localctx, 11);
				{
				setState(618);
				match(Surrogate_id_SYMB_2);
				setState(619);
				((PatternContext)_localctx).p_11_2 = pattern();
				setState(620);
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
		public TerminalNode Surrogate_id_SYMB_0() { return getToken(stellaParser.Surrogate_id_SYMB_0, 0); }
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
		enterRule(_localctx, 138, RULE_listPattern);
		try {
			setState(634);
			_errHandler.sync(this);
			switch ( getInterpreter().adaptivePredict(_input,17,_ctx) ) {
			case 1:
				enterOuterAlt(_localctx, 1);
				{
				 ((ListPatternContext)_localctx).result =  new stella.Absyn.ListPattern(); 
				}
				break;
			case 2:
				enterOuterAlt(_localctx, 2);
				{
				setState(626);
				((ListPatternContext)_localctx).p_2_1 = pattern();
				 ((ListPatternContext)_localctx).result =  new stella.Absyn.ListPattern(); _localctx.result.addLast(((ListPatternContext)_localctx).p_2_1.result); 
				}
				break;
			case 3:
				enterOuterAlt(_localctx, 3);
				{
				setState(629);
				((ListPatternContext)_localctx).p_3_1 = pattern();
				setState(630);
				match(Surrogate_id_SYMB_0);
				setState(631);
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
		enterRule(_localctx, 140, RULE_labelledPattern);
		try {
			enterOuterAlt(_localctx, 1);
			{
			setState(636);
			((LabelledPatternContext)_localctx).p_1_1 = match(StellaIdent);
			setState(637);
			match(Surrogate_id_SYMB_6);
			setState(638);
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
		public TerminalNode Surrogate_id_SYMB_0() { return getToken(stellaParser.Surrogate_id_SYMB_0, 0); }
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
		enterRule(_localctx, 142, RULE_listLabelledPattern);
		try {
			setState(650);
			_errHandler.sync(this);
			switch ( getInterpreter().adaptivePredict(_input,18,_ctx) ) {
			case 1:
				enterOuterAlt(_localctx, 1);
				{
				 ((ListLabelledPatternContext)_localctx).result =  new stella.Absyn.ListLabelledPattern(); 
				}
				break;
			case 2:
				enterOuterAlt(_localctx, 2);
				{
				setState(642);
				((ListLabelledPatternContext)_localctx).p_2_1 = labelledPattern();
				 ((ListLabelledPatternContext)_localctx).result =  new stella.Absyn.ListLabelledPattern(); _localctx.result.addLast(((ListLabelledPatternContext)_localctx).p_2_1.result); 
				}
				break;
			case 3:
				enterOuterAlt(_localctx, 3);
				{
				setState(645);
				((ListLabelledPatternContext)_localctx).p_3_1 = labelledPattern();
				setState(646);
				match(Surrogate_id_SYMB_0);
				setState(647);
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
		enterRule(_localctx, 144, RULE_binding);
		try {
			enterOuterAlt(_localctx, 1);
			{
			setState(652);
			((BindingContext)_localctx).p_1_1 = match(StellaIdent);
			setState(653);
			match(Surrogate_id_SYMB_6);
			setState(654);
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
		public TerminalNode Surrogate_id_SYMB_0() { return getToken(stellaParser.Surrogate_id_SYMB_0, 0); }
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
		enterRule(_localctx, 146, RULE_listBinding);
		try {
			setState(666);
			_errHandler.sync(this);
			switch ( getInterpreter().adaptivePredict(_input,19,_ctx) ) {
			case 1:
				enterOuterAlt(_localctx, 1);
				{
				 ((ListBindingContext)_localctx).result =  new stella.Absyn.ListBinding(); 
				}
				break;
			case 2:
				enterOuterAlt(_localctx, 2);
				{
				setState(658);
				((ListBindingContext)_localctx).p_2_1 = binding();
				 ((ListBindingContext)_localctx).result =  new stella.Absyn.ListBinding(); _localctx.result.addLast(((ListBindingContext)_localctx).p_2_1.result); 
				}
				break;
			case 3:
				enterOuterAlt(_localctx, 3);
				{
				setState(661);
				((ListBindingContext)_localctx).p_3_1 = binding();
				setState(662);
				match(Surrogate_id_SYMB_0);
				setState(663);
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

	public static class Expr1Context extends ParserRuleContext {
		public stella.Absyn.Expr result;
		public Expr2Context p_1_1;
		public Expr2Context p_1_3;
		public Expr2Context p_2_1;
		public Expr2Context p_2_3;
		public Expr2Context p_3_1;
		public Expr2Context p_3_3;
		public Expr2Context p_4_1;
		public Expr2Context p_4_3;
		public Expr2Context p_5_1;
		public Expr2Context p_5_3;
		public Expr2Context p_6_1;
		public Expr2Context p_6_3;
		public Expr2Context p_7_1;
		public TerminalNode Surrogate_id_SYMB_14() { return getToken(stellaParser.Surrogate_id_SYMB_14, 0); }
		public List<Expr2Context> expr2() {
			return getRuleContexts(Expr2Context.class);
		}
		public Expr2Context expr2(int i) {
			return getRuleContext(Expr2Context.class,i);
		}
		public TerminalNode Surrogate_id_SYMB_15() { return getToken(stellaParser.Surrogate_id_SYMB_15, 0); }
		public TerminalNode Surrogate_id_SYMB_16() { return getToken(stellaParser.Surrogate_id_SYMB_16, 0); }
		public TerminalNode Surrogate_id_SYMB_17() { return getToken(stellaParser.Surrogate_id_SYMB_17, 0); }
		public TerminalNode Surrogate_id_SYMB_18() { return getToken(stellaParser.Surrogate_id_SYMB_18, 0); }
		public TerminalNode Surrogate_id_SYMB_19() { return getToken(stellaParser.Surrogate_id_SYMB_19, 0); }
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
		Expr1Context _localctx = new Expr1Context(_ctx, getState());
		enterRule(_localctx, 148, RULE_expr1);
		try {
			setState(701);
			_errHandler.sync(this);
			switch ( getInterpreter().adaptivePredict(_input,20,_ctx) ) {
			case 1:
				enterOuterAlt(_localctx, 1);
				{
				setState(668);
				((Expr1Context)_localctx).p_1_1 = expr2(0);
				setState(669);
				match(Surrogate_id_SYMB_14);
				setState(670);
				((Expr1Context)_localctx).p_1_3 = expr2(0);
				 ((Expr1Context)_localctx).result =  new stella.Absyn.LessThan(((Expr1Context)_localctx).p_1_1.result,((Expr1Context)_localctx).p_1_3.result); 
				}
				break;
			case 2:
				enterOuterAlt(_localctx, 2);
				{
				setState(673);
				((Expr1Context)_localctx).p_2_1 = expr2(0);
				setState(674);
				match(Surrogate_id_SYMB_15);
				setState(675);
				((Expr1Context)_localctx).p_2_3 = expr2(0);
				 ((Expr1Context)_localctx).result =  new stella.Absyn.LessThanOrEqual(((Expr1Context)_localctx).p_2_1.result,((Expr1Context)_localctx).p_2_3.result); 
				}
				break;
			case 3:
				enterOuterAlt(_localctx, 3);
				{
				setState(678);
				((Expr1Context)_localctx).p_3_1 = expr2(0);
				setState(679);
				match(Surrogate_id_SYMB_16);
				setState(680);
				((Expr1Context)_localctx).p_3_3 = expr2(0);
				 ((Expr1Context)_localctx).result =  new stella.Absyn.GreaterThan(((Expr1Context)_localctx).p_3_1.result,((Expr1Context)_localctx).p_3_3.result); 
				}
				break;
			case 4:
				enterOuterAlt(_localctx, 4);
				{
				setState(683);
				((Expr1Context)_localctx).p_4_1 = expr2(0);
				setState(684);
				match(Surrogate_id_SYMB_17);
				setState(685);
				((Expr1Context)_localctx).p_4_3 = expr2(0);
				 ((Expr1Context)_localctx).result =  new stella.Absyn.GreaterThanOrEqual(((Expr1Context)_localctx).p_4_1.result,((Expr1Context)_localctx).p_4_3.result); 
				}
				break;
			case 5:
				enterOuterAlt(_localctx, 5);
				{
				setState(688);
				((Expr1Context)_localctx).p_5_1 = expr2(0);
				setState(689);
				match(Surrogate_id_SYMB_18);
				setState(690);
				((Expr1Context)_localctx).p_5_3 = expr2(0);
				 ((Expr1Context)_localctx).result =  new stella.Absyn.Equal(((Expr1Context)_localctx).p_5_1.result,((Expr1Context)_localctx).p_5_3.result); 
				}
				break;
			case 6:
				enterOuterAlt(_localctx, 6);
				{
				setState(693);
				((Expr1Context)_localctx).p_6_1 = expr2(0);
				setState(694);
				match(Surrogate_id_SYMB_19);
				setState(695);
				((Expr1Context)_localctx).p_6_3 = expr2(0);
				 ((Expr1Context)_localctx).result =  new stella.Absyn.NotEqual(((Expr1Context)_localctx).p_6_1.result,((Expr1Context)_localctx).p_6_3.result); 
				}
				break;
			case 7:
				enterOuterAlt(_localctx, 7);
				{
				setState(698);
				((Expr1Context)_localctx).p_7_1 = expr2(0);
				 ((Expr1Context)_localctx).result =  ((Expr1Context)_localctx).p_7_1.result; 
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

	public static class Expr2Context extends ParserRuleContext {
		public stella.Absyn.Expr result;
		public Expr2Context p_1_1;
		public Expr2Context p_8_1;
		public Expr2Context p_9_1;
		public ListParamDeclContext p_2_3;
		public ExprContext p_2_7;
		public ListExprContext p_3_2;
		public ListBindingContext p_4_3;
		public Token p_5_2;
		public ExprDataContext p_5_3;
		public Expr1Context p_6_2;
		public ListMatchCaseContext p_6_4;
		public ListExprContext p_7_2;
		public Expr3Context p_10_1;
		public TypeContext p_1_3;
		public Expr3Context p_8_3;
		public Expr3Context p_9_3;
		public TerminalNode Surrogate_id_SYMB_40() { return getToken(stellaParser.Surrogate_id_SYMB_40, 0); }
		public TerminalNode Surrogate_id_SYMB_2() { return getToken(stellaParser.Surrogate_id_SYMB_2, 0); }
		public TerminalNode Surrogate_id_SYMB_3() { return getToken(stellaParser.Surrogate_id_SYMB_3, 0); }
		public TerminalNode Surrogate_id_SYMB_4() { return getToken(stellaParser.Surrogate_id_SYMB_4, 0); }
		public TerminalNode Surrogate_id_SYMB_51() { return getToken(stellaParser.Surrogate_id_SYMB_51, 0); }
		public TerminalNode Surrogate_id_SYMB_1() { return getToken(stellaParser.Surrogate_id_SYMB_1, 0); }
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
		public TerminalNode Surrogate_id_SYMB_50() { return getToken(stellaParser.Surrogate_id_SYMB_50, 0); }
		public ListBindingContext listBinding() {
			return getRuleContext(ListBindingContext.class,0);
		}
		public TerminalNode Surrogate_id_SYMB_10() { return getToken(stellaParser.Surrogate_id_SYMB_10, 0); }
		public TerminalNode Surrogate_id_SYMB_11() { return getToken(stellaParser.Surrogate_id_SYMB_11, 0); }
		public TerminalNode StellaIdent() { return getToken(stellaParser.StellaIdent, 0); }
		public ExprDataContext exprData() {
			return getRuleContext(ExprDataContext.class,0);
		}
		public TerminalNode Surrogate_id_SYMB_47() { return getToken(stellaParser.Surrogate_id_SYMB_47, 0); }
		public Expr1Context expr1() {
			return getRuleContext(Expr1Context.class,0);
		}
		public ListMatchCaseContext listMatchCase() {
			return getRuleContext(ListMatchCaseContext.class,0);
		}
		public TerminalNode Surrogate_id_SYMB_12() { return getToken(stellaParser.Surrogate_id_SYMB_12, 0); }
		public TerminalNode Surrogate_id_SYMB_13() { return getToken(stellaParser.Surrogate_id_SYMB_13, 0); }
		public Expr3Context expr3() {
			return getRuleContext(Expr3Context.class,0);
		}
		public TerminalNode Surrogate_id_SYMB_33() { return getToken(stellaParser.Surrogate_id_SYMB_33, 0); }
		public Expr2Context expr2() {
			return getRuleContext(Expr2Context.class,0);
		}
		public TypeContext type() {
			return getRuleContext(TypeContext.class,0);
		}
		public TerminalNode Surrogate_id_SYMB_20() { return getToken(stellaParser.Surrogate_id_SYMB_20, 0); }
		public TerminalNode Surrogate_id_SYMB_49() { return getToken(stellaParser.Surrogate_id_SYMB_49, 0); }
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
		int _startState = 150;
		enterRecursionRule(_localctx, 150, RULE_expr2, _p);
		try {
			int _alt;
			enterOuterAlt(_localctx, 1);
			{
			setState(747);
			_errHandler.sync(this);
			switch (_input.LA(1)) {
			case Surrogate_id_SYMB_40:
				{
				setState(704);
				match(Surrogate_id_SYMB_40);
				setState(705);
				match(Surrogate_id_SYMB_2);
				setState(706);
				((Expr2Context)_localctx).p_2_3 = listParamDecl();
				setState(707);
				match(Surrogate_id_SYMB_3);
				setState(708);
				match(Surrogate_id_SYMB_4);
				setState(709);
				match(Surrogate_id_SYMB_51);
				setState(710);
				((Expr2Context)_localctx).p_2_7 = expr();
				setState(711);
				match(Surrogate_id_SYMB_1);
				setState(712);
				match(Surrogate_id_SYMB_5);
				 ((Expr2Context)_localctx).result =  new stella.Absyn.Abstraction(((Expr2Context)_localctx).p_2_3.result,((Expr2Context)_localctx).p_2_7.result); 
				}
				break;
			case Surrogate_id_SYMB_4:
				{
				setState(715);
				match(Surrogate_id_SYMB_4);
				setState(716);
				((Expr2Context)_localctx).p_3_2 = listExpr();
				setState(717);
				match(Surrogate_id_SYMB_5);
				 ((Expr2Context)_localctx).result =  new stella.Absyn.Tuple(((Expr2Context)_localctx).p_3_2.result); 
				}
				break;
			case Surrogate_id_SYMB_50:
				{
				setState(720);
				match(Surrogate_id_SYMB_50);
				setState(721);
				match(Surrogate_id_SYMB_4);
				setState(722);
				((Expr2Context)_localctx).p_4_3 = listBinding();
				setState(723);
				match(Surrogate_id_SYMB_5);
				 ((Expr2Context)_localctx).result =  new stella.Absyn.Record(((Expr2Context)_localctx).p_4_3.result); 
				}
				break;
			case Surrogate_id_SYMB_10:
				{
				setState(726);
				match(Surrogate_id_SYMB_10);
				setState(727);
				((Expr2Context)_localctx).p_5_2 = match(StellaIdent);
				setState(728);
				((Expr2Context)_localctx).p_5_3 = exprData();
				setState(729);
				match(Surrogate_id_SYMB_11);
				 ((Expr2Context)_localctx).result =  new stella.Absyn.Variant(((Expr2Context)_localctx).p_5_2.getText(),((Expr2Context)_localctx).p_5_3.result); 
				}
				break;
			case Surrogate_id_SYMB_47:
				{
				setState(732);
				match(Surrogate_id_SYMB_47);
				setState(733);
				((Expr2Context)_localctx).p_6_2 = expr1();
				setState(734);
				match(Surrogate_id_SYMB_4);
				setState(735);
				((Expr2Context)_localctx).p_6_4 = listMatchCase();
				setState(736);
				match(Surrogate_id_SYMB_5);
				 ((Expr2Context)_localctx).result =  new stella.Absyn.Match(((Expr2Context)_localctx).p_6_2.result,((Expr2Context)_localctx).p_6_4.result); 
				}
				break;
			case Surrogate_id_SYMB_12:
				{
				setState(739);
				match(Surrogate_id_SYMB_12);
				setState(740);
				((Expr2Context)_localctx).p_7_2 = listExpr();
				setState(741);
				match(Surrogate_id_SYMB_13);
				 ((Expr2Context)_localctx).result =  new stella.Absyn.List(((Expr2Context)_localctx).p_7_2.result); 
				}
				break;
			case Surrogate_id_SYMB_2:
			case Surrogate_id_SYMB_22:
			case Surrogate_id_SYMB_23:
			case Surrogate_id_SYMB_24:
			case Surrogate_id_SYMB_25:
			case Surrogate_id_SYMB_26:
			case Surrogate_id_SYMB_27:
			case Surrogate_id_SYMB_34:
			case Surrogate_id_SYMB_38:
			case Surrogate_id_SYMB_39:
			case Surrogate_id_SYMB_41:
			case Surrogate_id_SYMB_48:
			case Surrogate_id_SYMB_52:
			case Surrogate_id_SYMB_55:
			case Surrogate_id_SYMB_57:
			case StellaIdent:
			case INTEGER:
				{
				setState(744);
				((Expr2Context)_localctx).p_10_1 = expr3(0);
				 ((Expr2Context)_localctx).result =  ((Expr2Context)_localctx).p_10_1.result; 
				}
				break;
			default:
				throw new NoViableAltException(this);
			}
			_ctx.stop = _input.LT(-1);
			setState(766);
			_errHandler.sync(this);
			_alt = getInterpreter().adaptivePredict(_input,23,_ctx);
			while ( _alt!=2 && _alt!=org.antlr.v4.runtime.atn.ATN.INVALID_ALT_NUMBER ) {
				if ( _alt==1 ) {
					if ( _parseListeners!=null ) triggerExitRuleEvent();
					_prevctx = _localctx;
					{
					setState(764);
					_errHandler.sync(this);
					switch ( getInterpreter().adaptivePredict(_input,22,_ctx) ) {
					case 1:
						{
						_localctx = new Expr2Context(_parentctx, _parentState);
						_localctx.p_1_1 = _prevctx;
						_localctx.p_1_1 = _prevctx;
						pushNewRecursionContext(_localctx, _startState, RULE_expr2);
						setState(749);
						if (!(precpred(_ctx, 10))) throw new FailedPredicateException(this, "precpred(_ctx, 10)");
						setState(750);
						match(Surrogate_id_SYMB_33);
						setState(751);
						((Expr2Context)_localctx).p_1_3 = type();
						 ((Expr2Context)_localctx).result =  new stella.Absyn.TypeAsc(((Expr2Context)_localctx).p_1_1.result,((Expr2Context)_localctx).p_1_3.result); 
						}
						break;
					case 2:
						{
						_localctx = new Expr2Context(_parentctx, _parentState);
						_localctx.p_8_1 = _prevctx;
						_localctx.p_8_1 = _prevctx;
						pushNewRecursionContext(_localctx, _startState, RULE_expr2);
						setState(754);
						if (!(precpred(_ctx, 3))) throw new FailedPredicateException(this, "precpred(_ctx, 3)");
						setState(755);
						match(Surrogate_id_SYMB_20);
						setState(756);
						((Expr2Context)_localctx).p_8_3 = expr3(0);
						 ((Expr2Context)_localctx).result =  new stella.Absyn.Add(((Expr2Context)_localctx).p_8_1.result,((Expr2Context)_localctx).p_8_3.result); 
						}
						break;
					case 3:
						{
						_localctx = new Expr2Context(_parentctx, _parentState);
						_localctx.p_9_1 = _prevctx;
						_localctx.p_9_1 = _prevctx;
						pushNewRecursionContext(_localctx, _startState, RULE_expr2);
						setState(759);
						if (!(precpred(_ctx, 2))) throw new FailedPredicateException(this, "precpred(_ctx, 2)");
						setState(760);
						match(Surrogate_id_SYMB_49);
						setState(761);
						((Expr2Context)_localctx).p_9_3 = expr3(0);
						 ((Expr2Context)_localctx).result =  new stella.Absyn.LogicOr(((Expr2Context)_localctx).p_9_1.result,((Expr2Context)_localctx).p_9_3.result); 
						}
						break;
					}
					} 
				}
				setState(768);
				_errHandler.sync(this);
				_alt = getInterpreter().adaptivePredict(_input,23,_ctx);
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
		public Expr3Context p_2_1;
		public Expr4Context p_3_1;
		public Expr4Context p_1_3;
		public Expr4Context p_2_3;
		public Expr4Context expr4() {
			return getRuleContext(Expr4Context.class,0);
		}
		public TerminalNode Surrogate_id_SYMB_21() { return getToken(stellaParser.Surrogate_id_SYMB_21, 0); }
		public Expr3Context expr3() {
			return getRuleContext(Expr3Context.class,0);
		}
		public TerminalNode Surrogate_id_SYMB_32() { return getToken(stellaParser.Surrogate_id_SYMB_32, 0); }
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
		int _startState = 152;
		enterRecursionRule(_localctx, 152, RULE_expr3, _p);
		try {
			int _alt;
			enterOuterAlt(_localctx, 1);
			{
			{
			setState(770);
			((Expr3Context)_localctx).p_3_1 = expr4(0);
			 ((Expr3Context)_localctx).result =  ((Expr3Context)_localctx).p_3_1.result; 
			}
			_ctx.stop = _input.LT(-1);
			setState(785);
			_errHandler.sync(this);
			_alt = getInterpreter().adaptivePredict(_input,25,_ctx);
			while ( _alt!=2 && _alt!=org.antlr.v4.runtime.atn.ATN.INVALID_ALT_NUMBER ) {
				if ( _alt==1 ) {
					if ( _parseListeners!=null ) triggerExitRuleEvent();
					_prevctx = _localctx;
					{
					setState(783);
					_errHandler.sync(this);
					switch ( getInterpreter().adaptivePredict(_input,24,_ctx) ) {
					case 1:
						{
						_localctx = new Expr3Context(_parentctx, _parentState);
						_localctx.p_1_1 = _prevctx;
						_localctx.p_1_1 = _prevctx;
						pushNewRecursionContext(_localctx, _startState, RULE_expr3);
						setState(773);
						if (!(precpred(_ctx, 3))) throw new FailedPredicateException(this, "precpred(_ctx, 3)");
						setState(774);
						match(Surrogate_id_SYMB_21);
						setState(775);
						((Expr3Context)_localctx).p_1_3 = expr4(0);
						 ((Expr3Context)_localctx).result =  new stella.Absyn.Multiply(((Expr3Context)_localctx).p_1_1.result,((Expr3Context)_localctx).p_1_3.result); 
						}
						break;
					case 2:
						{
						_localctx = new Expr3Context(_parentctx, _parentState);
						_localctx.p_2_1 = _prevctx;
						_localctx.p_2_1 = _prevctx;
						pushNewRecursionContext(_localctx, _startState, RULE_expr3);
						setState(778);
						if (!(precpred(_ctx, 2))) throw new FailedPredicateException(this, "precpred(_ctx, 2)");
						setState(779);
						match(Surrogate_id_SYMB_32);
						setState(780);
						((Expr3Context)_localctx).p_2_3 = expr4(0);
						 ((Expr3Context)_localctx).result =  new stella.Absyn.LogicAnd(((Expr3Context)_localctx).p_2_1.result,((Expr3Context)_localctx).p_2_3.result); 
						}
						break;
					}
					} 
				}
				setState(787);
				_errHandler.sync(this);
				_alt = getInterpreter().adaptivePredict(_input,25,_ctx);
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
		public Expr4Context p_1_1;
		public Expr5Context p_2_1;
		public ListExprContext p_1_3;
		public Expr5Context expr5() {
			return getRuleContext(Expr5Context.class,0);
		}
		public TerminalNode Surrogate_id_SYMB_2() { return getToken(stellaParser.Surrogate_id_SYMB_2, 0); }
		public TerminalNode Surrogate_id_SYMB_3() { return getToken(stellaParser.Surrogate_id_SYMB_3, 0); }
		public Expr4Context expr4() {
			return getRuleContext(Expr4Context.class,0);
		}
		public ListExprContext listExpr() {
			return getRuleContext(ListExprContext.class,0);
		}
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
		return expr4(0);
	}

	private Expr4Context expr4(int _p) throws RecognitionException {
		ParserRuleContext _parentctx = _ctx;
		int _parentState = getState();
		Expr4Context _localctx = new Expr4Context(_ctx, _parentState);
		Expr4Context _prevctx = _localctx;
		int _startState = 154;
		enterRecursionRule(_localctx, 154, RULE_expr4, _p);
		try {
			int _alt;
			enterOuterAlt(_localctx, 1);
			{
			{
			setState(789);
			((Expr4Context)_localctx).p_2_1 = expr5();
			 ((Expr4Context)_localctx).result =  ((Expr4Context)_localctx).p_2_1.result; 
			}
			_ctx.stop = _input.LT(-1);
			setState(800);
			_errHandler.sync(this);
			_alt = getInterpreter().adaptivePredict(_input,26,_ctx);
			while ( _alt!=2 && _alt!=org.antlr.v4.runtime.atn.ATN.INVALID_ALT_NUMBER ) {
				if ( _alt==1 ) {
					if ( _parseListeners!=null ) triggerExitRuleEvent();
					_prevctx = _localctx;
					{
					{
					_localctx = new Expr4Context(_parentctx, _parentState);
					_localctx.p_1_1 = _prevctx;
					_localctx.p_1_1 = _prevctx;
					pushNewRecursionContext(_localctx, _startState, RULE_expr4);
					setState(792);
					if (!(precpred(_ctx, 2))) throw new FailedPredicateException(this, "precpred(_ctx, 2)");
					setState(793);
					match(Surrogate_id_SYMB_2);
					setState(794);
					((Expr4Context)_localctx).p_1_3 = listExpr();
					setState(795);
					match(Surrogate_id_SYMB_3);
					 ((Expr4Context)_localctx).result =  new stella.Absyn.Application(((Expr4Context)_localctx).p_1_1.result,((Expr4Context)_localctx).p_1_3.result); 
					}
					} 
				}
				setState(802);
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

	public static class Expr5Context extends ParserRuleContext {
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
		public Expr6Context p_11_5;
		public TypeContext p_12_3;
		public Expr6Context p_12_5;
		public Expr6Context p_13_1;
		public TerminalNode Surrogate_id_SYMB_34() { return getToken(stellaParser.Surrogate_id_SYMB_34, 0); }
		public TerminalNode Surrogate_id_SYMB_2() { return getToken(stellaParser.Surrogate_id_SYMB_2, 0); }
		public List<TerminalNode> Surrogate_id_SYMB_0() { return getTokens(stellaParser.Surrogate_id_SYMB_0); }
		public TerminalNode Surrogate_id_SYMB_0(int i) {
			return getToken(stellaParser.Surrogate_id_SYMB_0, i);
		}
		public TerminalNode Surrogate_id_SYMB_3() { return getToken(stellaParser.Surrogate_id_SYMB_3, 0); }
		public List<ExprContext> expr() {
			return getRuleContexts(ExprContext.class);
		}
		public ExprContext expr(int i) {
			return getRuleContext(ExprContext.class,i);
		}
		public TerminalNode Surrogate_id_SYMB_22() { return getToken(stellaParser.Surrogate_id_SYMB_22, 0); }
		public TerminalNode Surrogate_id_SYMB_23() { return getToken(stellaParser.Surrogate_id_SYMB_23, 0); }
		public TerminalNode Surrogate_id_SYMB_24() { return getToken(stellaParser.Surrogate_id_SYMB_24, 0); }
		public TerminalNode Surrogate_id_SYMB_52() { return getToken(stellaParser.Surrogate_id_SYMB_52, 0); }
		public TerminalNode Surrogate_id_SYMB_48() { return getToken(stellaParser.Surrogate_id_SYMB_48, 0); }
		public TerminalNode Surrogate_id_SYMB_25() { return getToken(stellaParser.Surrogate_id_SYMB_25, 0); }
		public TerminalNode Surrogate_id_SYMB_26() { return getToken(stellaParser.Surrogate_id_SYMB_26, 0); }
		public TerminalNode Surrogate_id_SYMB_39() { return getToken(stellaParser.Surrogate_id_SYMB_39, 0); }
		public TerminalNode Surrogate_id_SYMB_27() { return getToken(stellaParser.Surrogate_id_SYMB_27, 0); }
		public TerminalNode Surrogate_id_SYMB_41() { return getToken(stellaParser.Surrogate_id_SYMB_41, 0); }
		public TerminalNode Surrogate_id_SYMB_12() { return getToken(stellaParser.Surrogate_id_SYMB_12, 0); }
		public TerminalNode Surrogate_id_SYMB_13() { return getToken(stellaParser.Surrogate_id_SYMB_13, 0); }
		public TypeContext type() {
			return getRuleContext(TypeContext.class,0);
		}
		public Expr6Context expr6() {
			return getRuleContext(Expr6Context.class,0);
		}
		public TerminalNode Surrogate_id_SYMB_57() { return getToken(stellaParser.Surrogate_id_SYMB_57, 0); }
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
		Expr5Context _localctx = new Expr5Context(_ctx, getState());
		enterRule(_localctx, 156, RULE_expr5);
		try {
			setState(886);
			_errHandler.sync(this);
			switch (_input.LA(1)) {
			case Surrogate_id_SYMB_34:
				enterOuterAlt(_localctx, 1);
				{
				setState(803);
				match(Surrogate_id_SYMB_34);
				setState(804);
				match(Surrogate_id_SYMB_2);
				setState(805);
				((Expr5Context)_localctx).p_1_3 = expr();
				setState(806);
				match(Surrogate_id_SYMB_0);
				setState(807);
				((Expr5Context)_localctx).p_1_5 = expr();
				setState(808);
				match(Surrogate_id_SYMB_3);
				 ((Expr5Context)_localctx).result =  new stella.Absyn.ConsList(((Expr5Context)_localctx).p_1_3.result,((Expr5Context)_localctx).p_1_5.result); 
				}
				break;
			case Surrogate_id_SYMB_22:
				enterOuterAlt(_localctx, 2);
				{
				setState(811);
				match(Surrogate_id_SYMB_22);
				setState(812);
				match(Surrogate_id_SYMB_2);
				setState(813);
				((Expr5Context)_localctx).p_2_3 = expr();
				setState(814);
				match(Surrogate_id_SYMB_3);
				 ((Expr5Context)_localctx).result =  new stella.Absyn.Head(((Expr5Context)_localctx).p_2_3.result); 
				}
				break;
			case Surrogate_id_SYMB_23:
				enterOuterAlt(_localctx, 3);
				{
				setState(817);
				match(Surrogate_id_SYMB_23);
				setState(818);
				match(Surrogate_id_SYMB_2);
				setState(819);
				((Expr5Context)_localctx).p_3_3 = expr();
				setState(820);
				match(Surrogate_id_SYMB_3);
				 ((Expr5Context)_localctx).result =  new stella.Absyn.IsEmpty(((Expr5Context)_localctx).p_3_3.result); 
				}
				break;
			case Surrogate_id_SYMB_24:
				enterOuterAlt(_localctx, 4);
				{
				setState(823);
				match(Surrogate_id_SYMB_24);
				setState(824);
				match(Surrogate_id_SYMB_2);
				setState(825);
				((Expr5Context)_localctx).p_4_3 = expr();
				setState(826);
				match(Surrogate_id_SYMB_3);
				 ((Expr5Context)_localctx).result =  new stella.Absyn.Tail(((Expr5Context)_localctx).p_4_3.result); 
				}
				break;
			case Surrogate_id_SYMB_52:
				enterOuterAlt(_localctx, 5);
				{
				setState(829);
				match(Surrogate_id_SYMB_52);
				setState(830);
				match(Surrogate_id_SYMB_2);
				setState(831);
				((Expr5Context)_localctx).p_5_3 = expr();
				setState(832);
				match(Surrogate_id_SYMB_3);
				 ((Expr5Context)_localctx).result =  new stella.Absyn.Succ(((Expr5Context)_localctx).p_5_3.result); 
				}
				break;
			case Surrogate_id_SYMB_48:
				enterOuterAlt(_localctx, 6);
				{
				setState(835);
				match(Surrogate_id_SYMB_48);
				setState(836);
				match(Surrogate_id_SYMB_2);
				setState(837);
				((Expr5Context)_localctx).p_6_3 = expr();
				setState(838);
				match(Surrogate_id_SYMB_3);
				 ((Expr5Context)_localctx).result =  new stella.Absyn.LogicNot(((Expr5Context)_localctx).p_6_3.result); 
				}
				break;
			case Surrogate_id_SYMB_25:
				enterOuterAlt(_localctx, 7);
				{
				setState(841);
				match(Surrogate_id_SYMB_25);
				setState(842);
				match(Surrogate_id_SYMB_2);
				setState(843);
				((Expr5Context)_localctx).p_7_3 = expr();
				setState(844);
				match(Surrogate_id_SYMB_3);
				 ((Expr5Context)_localctx).result =  new stella.Absyn.Pred(((Expr5Context)_localctx).p_7_3.result); 
				}
				break;
			case Surrogate_id_SYMB_26:
				enterOuterAlt(_localctx, 8);
				{
				setState(847);
				match(Surrogate_id_SYMB_26);
				setState(848);
				match(Surrogate_id_SYMB_2);
				setState(849);
				((Expr5Context)_localctx).p_8_3 = expr();
				setState(850);
				match(Surrogate_id_SYMB_3);
				 ((Expr5Context)_localctx).result =  new stella.Absyn.IsZero(((Expr5Context)_localctx).p_8_3.result); 
				}
				break;
			case Surrogate_id_SYMB_39:
				enterOuterAlt(_localctx, 9);
				{
				setState(853);
				match(Surrogate_id_SYMB_39);
				setState(854);
				match(Surrogate_id_SYMB_2);
				setState(855);
				((Expr5Context)_localctx).p_9_3 = expr();
				setState(856);
				match(Surrogate_id_SYMB_3);
				 ((Expr5Context)_localctx).result =  new stella.Absyn.Fix(((Expr5Context)_localctx).p_9_3.result); 
				}
				break;
			case Surrogate_id_SYMB_27:
				enterOuterAlt(_localctx, 10);
				{
				setState(859);
				match(Surrogate_id_SYMB_27);
				setState(860);
				match(Surrogate_id_SYMB_2);
				setState(861);
				((Expr5Context)_localctx).p_10_3 = expr();
				setState(862);
				match(Surrogate_id_SYMB_0);
				setState(863);
				((Expr5Context)_localctx).p_10_5 = expr();
				setState(864);
				match(Surrogate_id_SYMB_0);
				setState(865);
				((Expr5Context)_localctx).p_10_7 = expr();
				setState(866);
				match(Surrogate_id_SYMB_3);
				 ((Expr5Context)_localctx).result =  new stella.Absyn.NatRec(((Expr5Context)_localctx).p_10_3.result,((Expr5Context)_localctx).p_10_5.result,((Expr5Context)_localctx).p_10_7.result); 
				}
				break;
			case Surrogate_id_SYMB_41:
				enterOuterAlt(_localctx, 11);
				{
				setState(869);
				match(Surrogate_id_SYMB_41);
				setState(870);
				match(Surrogate_id_SYMB_12);
				setState(871);
				((Expr5Context)_localctx).p_11_3 = type();
				setState(872);
				match(Surrogate_id_SYMB_13);
				setState(873);
				((Expr5Context)_localctx).p_11_5 = expr6(0);
				 ((Expr5Context)_localctx).result =  new stella.Absyn.Fold(((Expr5Context)_localctx).p_11_3.result,((Expr5Context)_localctx).p_11_5.result); 
				}
				break;
			case Surrogate_id_SYMB_57:
				enterOuterAlt(_localctx, 12);
				{
				setState(876);
				match(Surrogate_id_SYMB_57);
				setState(877);
				match(Surrogate_id_SYMB_12);
				setState(878);
				((Expr5Context)_localctx).p_12_3 = type();
				setState(879);
				match(Surrogate_id_SYMB_13);
				setState(880);
				((Expr5Context)_localctx).p_12_5 = expr6(0);
				 ((Expr5Context)_localctx).result =  new stella.Absyn.Unfold(((Expr5Context)_localctx).p_12_3.result,((Expr5Context)_localctx).p_12_5.result); 
				}
				break;
			case Surrogate_id_SYMB_2:
			case Surrogate_id_SYMB_38:
			case Surrogate_id_SYMB_55:
			case StellaIdent:
			case INTEGER:
				enterOuterAlt(_localctx, 13);
				{
				setState(883);
				((Expr5Context)_localctx).p_13_1 = expr6(0);
				 ((Expr5Context)_localctx).result =  ((Expr5Context)_localctx).p_13_1.result; 
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

	public static class Expr6Context extends ParserRuleContext {
		public stella.Absyn.Expr result;
		public Expr6Context p_1_1;
		public Expr6Context p_2_1;
		public Token p_5_1;
		public Token p_6_1;
		public ExprContext p_7_2;
		public Token p_1_3;
		public Token p_2_3;
		public TerminalNode Surrogate_id_SYMB_55() { return getToken(stellaParser.Surrogate_id_SYMB_55, 0); }
		public TerminalNode Surrogate_id_SYMB_38() { return getToken(stellaParser.Surrogate_id_SYMB_38, 0); }
		public TerminalNode INTEGER() { return getToken(stellaParser.INTEGER, 0); }
		public TerminalNode StellaIdent() { return getToken(stellaParser.StellaIdent, 0); }
		public TerminalNode Surrogate_id_SYMB_2() { return getToken(stellaParser.Surrogate_id_SYMB_2, 0); }
		public TerminalNode Surrogate_id_SYMB_3() { return getToken(stellaParser.Surrogate_id_SYMB_3, 0); }
		public ExprContext expr() {
			return getRuleContext(ExprContext.class,0);
		}
		public TerminalNode Surrogate_id_SYMB_28() { return getToken(stellaParser.Surrogate_id_SYMB_28, 0); }
		public Expr6Context expr6() {
			return getRuleContext(Expr6Context.class,0);
		}
		public Expr6Context(ParserRuleContext parent, int invokingState) {
			super(parent, invokingState);
		}
		@Override public int getRuleIndex() { return RULE_expr6; }
		@Override
		public void enterRule(ParseTreeListener listener) {
			if ( listener instanceof stellaParserListener ) ((stellaParserListener)listener).enterExpr6(this);
		}
		@Override
		public void exitRule(ParseTreeListener listener) {
			if ( listener instanceof stellaParserListener ) ((stellaParserListener)listener).exitExpr6(this);
		}
	}

	public final Expr6Context expr6() throws RecognitionException {
		return expr6(0);
	}

	private Expr6Context expr6(int _p) throws RecognitionException {
		ParserRuleContext _parentctx = _ctx;
		int _parentState = getState();
		Expr6Context _localctx = new Expr6Context(_ctx, _parentState);
		Expr6Context _prevctx = _localctx;
		int _startState = 158;
		enterRecursionRule(_localctx, 158, RULE_expr6, _p);
		try {
			int _alt;
			enterOuterAlt(_localctx, 1);
			{
			setState(902);
			_errHandler.sync(this);
			switch (_input.LA(1)) {
			case Surrogate_id_SYMB_55:
				{
				setState(889);
				match(Surrogate_id_SYMB_55);
				 ((Expr6Context)_localctx).result =  new stella.Absyn.ConstTrue(); 
				}
				break;
			case Surrogate_id_SYMB_38:
				{
				setState(891);
				match(Surrogate_id_SYMB_38);
				 ((Expr6Context)_localctx).result =  new stella.Absyn.ConstFalse(); 
				}
				break;
			case INTEGER:
				{
				setState(893);
				((Expr6Context)_localctx).p_5_1 = match(INTEGER);
				 ((Expr6Context)_localctx).result =  new stella.Absyn.ConstInt(Integer.parseInt(((Expr6Context)_localctx).p_5_1.getText())); 
				}
				break;
			case StellaIdent:
				{
				setState(895);
				((Expr6Context)_localctx).p_6_1 = match(StellaIdent);
				 ((Expr6Context)_localctx).result =  new stella.Absyn.Var(((Expr6Context)_localctx).p_6_1.getText()); 
				}
				break;
			case Surrogate_id_SYMB_2:
				{
				setState(897);
				match(Surrogate_id_SYMB_2);
				setState(898);
				((Expr6Context)_localctx).p_7_2 = expr();
				setState(899);
				match(Surrogate_id_SYMB_3);
				 ((Expr6Context)_localctx).result =  ((Expr6Context)_localctx).p_7_2.result; 
				}
				break;
			default:
				throw new NoViableAltException(this);
			}
			_ctx.stop = _input.LT(-1);
			setState(914);
			_errHandler.sync(this);
			_alt = getInterpreter().adaptivePredict(_input,30,_ctx);
			while ( _alt!=2 && _alt!=org.antlr.v4.runtime.atn.ATN.INVALID_ALT_NUMBER ) {
				if ( _alt==1 ) {
					if ( _parseListeners!=null ) triggerExitRuleEvent();
					_prevctx = _localctx;
					{
					setState(912);
					_errHandler.sync(this);
					switch ( getInterpreter().adaptivePredict(_input,29,_ctx) ) {
					case 1:
						{
						_localctx = new Expr6Context(_parentctx, _parentState);
						_localctx.p_1_1 = _prevctx;
						_localctx.p_1_1 = _prevctx;
						pushNewRecursionContext(_localctx, _startState, RULE_expr6);
						setState(904);
						if (!(precpred(_ctx, 7))) throw new FailedPredicateException(this, "precpred(_ctx, 7)");
						setState(905);
						match(Surrogate_id_SYMB_28);
						setState(906);
						((Expr6Context)_localctx).p_1_3 = match(StellaIdent);
						 ((Expr6Context)_localctx).result =  new stella.Absyn.DotRecord(((Expr6Context)_localctx).p_1_1.result,((Expr6Context)_localctx).p_1_3.getText()); 
						}
						break;
					case 2:
						{
						_localctx = new Expr6Context(_parentctx, _parentState);
						_localctx.p_2_1 = _prevctx;
						_localctx.p_2_1 = _prevctx;
						pushNewRecursionContext(_localctx, _startState, RULE_expr6);
						setState(908);
						if (!(precpred(_ctx, 6))) throw new FailedPredicateException(this, "precpred(_ctx, 6)");
						setState(909);
						match(Surrogate_id_SYMB_28);
						setState(910);
						((Expr6Context)_localctx).p_2_3 = match(INTEGER);
						 ((Expr6Context)_localctx).result =  new stella.Absyn.DotTuple(((Expr6Context)_localctx).p_2_1.result,Integer.parseInt(((Expr6Context)_localctx).p_2_3.getText())); 
						}
						break;
					}
					} 
				}
				setState(916);
				_errHandler.sync(this);
				_alt = getInterpreter().adaptivePredict(_input,30,_ctx);
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
		public TerminalNode Surrogate_id_SYMB_40() { return getToken(stellaParser.Surrogate_id_SYMB_40, 0); }
		public TerminalNode Surrogate_id_SYMB_2() { return getToken(stellaParser.Surrogate_id_SYMB_2, 0); }
		public TerminalNode Surrogate_id_SYMB_3() { return getToken(stellaParser.Surrogate_id_SYMB_3, 0); }
		public TerminalNode Surrogate_id_SYMB_8() { return getToken(stellaParser.Surrogate_id_SYMB_8, 0); }
		public ListTypeContext listType() {
			return getRuleContext(ListTypeContext.class,0);
		}
		public TypeContext type() {
			return getRuleContext(TypeContext.class,0);
		}
		public TerminalNode Surrogate_id_SYMB_60() { return getToken(stellaParser.Surrogate_id_SYMB_60, 0); }
		public TerminalNode Surrogate_id_SYMB_28() { return getToken(stellaParser.Surrogate_id_SYMB_28, 0); }
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
		enterRule(_localctx, 160, RULE_type);
		try {
			setState(934);
			_errHandler.sync(this);
			switch (_input.LA(1)) {
			case Surrogate_id_SYMB_40:
				enterOuterAlt(_localctx, 1);
				{
				setState(917);
				match(Surrogate_id_SYMB_40);
				setState(918);
				match(Surrogate_id_SYMB_2);
				setState(919);
				((TypeContext)_localctx).p_1_3 = listType();
				setState(920);
				match(Surrogate_id_SYMB_3);
				setState(921);
				match(Surrogate_id_SYMB_8);
				setState(922);
				((TypeContext)_localctx).p_1_6 = type();
				 ((TypeContext)_localctx).result =  new stella.Absyn.TypeFun(((TypeContext)_localctx).p_1_3.result,((TypeContext)_localctx).p_1_6.result); 
				}
				break;
			case Surrogate_id_SYMB_60:
				enterOuterAlt(_localctx, 2);
				{
				setState(925);
				match(Surrogate_id_SYMB_60);
				setState(926);
				((TypeContext)_localctx).p_2_2 = match(StellaIdent);
				setState(927);
				match(Surrogate_id_SYMB_28);
				setState(928);
				((TypeContext)_localctx).p_2_4 = type();
				 ((TypeContext)_localctx).result =  new stella.Absyn.TypeRec(((TypeContext)_localctx).p_2_2.getText(),((TypeContext)_localctx).p_2_4.result); 
				}
				break;
			case Surrogate_id_SYMB_2:
			case Surrogate_id_SYMB_4:
			case Surrogate_id_SYMB_12:
			case Surrogate_id_SYMB_29:
			case Surrogate_id_SYMB_30:
			case Surrogate_id_SYMB_31:
			case Surrogate_id_SYMB_50:
			case Surrogate_id_SYMB_58:
			case StellaIdent:
				enterOuterAlt(_localctx, 3);
				{
				setState(931);
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
		public Type2Context p_1_1;
		public Type2Context p_1_3;
		public Type2Context p_2_1;
		public TerminalNode Surrogate_id_SYMB_20() { return getToken(stellaParser.Surrogate_id_SYMB_20, 0); }
		public List<Type2Context> type2() {
			return getRuleContexts(Type2Context.class);
		}
		public Type2Context type2(int i) {
			return getRuleContext(Type2Context.class,i);
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
		enterRule(_localctx, 162, RULE_type1);
		try {
			setState(944);
			_errHandler.sync(this);
			switch ( getInterpreter().adaptivePredict(_input,32,_ctx) ) {
			case 1:
				enterOuterAlt(_localctx, 1);
				{
				setState(936);
				((Type1Context)_localctx).p_1_1 = type2();
				setState(937);
				match(Surrogate_id_SYMB_20);
				setState(938);
				((Type1Context)_localctx).p_1_3 = type2();
				 ((Type1Context)_localctx).result =  new stella.Absyn.TypeSum(((Type1Context)_localctx).p_1_1.result,((Type1Context)_localctx).p_1_3.result); 
				}
				break;
			case 2:
				enterOuterAlt(_localctx, 2);
				{
				setState(941);
				((Type1Context)_localctx).p_2_1 = type2();
				 ((Type1Context)_localctx).result =  ((Type1Context)_localctx).p_2_1.result; 
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

	public static class Type2Context extends ParserRuleContext {
		public stella.Absyn.Type result;
		public ListTypeContext p_1_2;
		public ListRecordFieldTypeContext p_2_3;
		public ListVariantFieldTypeContext p_3_3;
		public TypeContext p_4_2;
		public Type3Context p_5_1;
		public TerminalNode Surrogate_id_SYMB_4() { return getToken(stellaParser.Surrogate_id_SYMB_4, 0); }
		public TerminalNode Surrogate_id_SYMB_5() { return getToken(stellaParser.Surrogate_id_SYMB_5, 0); }
		public ListTypeContext listType() {
			return getRuleContext(ListTypeContext.class,0);
		}
		public TerminalNode Surrogate_id_SYMB_50() { return getToken(stellaParser.Surrogate_id_SYMB_50, 0); }
		public ListRecordFieldTypeContext listRecordFieldType() {
			return getRuleContext(ListRecordFieldTypeContext.class,0);
		}
		public TerminalNode Surrogate_id_SYMB_58() { return getToken(stellaParser.Surrogate_id_SYMB_58, 0); }
		public TerminalNode Surrogate_id_SYMB_10() { return getToken(stellaParser.Surrogate_id_SYMB_10, 0); }
		public TerminalNode Surrogate_id_SYMB_11() { return getToken(stellaParser.Surrogate_id_SYMB_11, 0); }
		public ListVariantFieldTypeContext listVariantFieldType() {
			return getRuleContext(ListVariantFieldTypeContext.class,0);
		}
		public TerminalNode Surrogate_id_SYMB_12() { return getToken(stellaParser.Surrogate_id_SYMB_12, 0); }
		public TerminalNode Surrogate_id_SYMB_13() { return getToken(stellaParser.Surrogate_id_SYMB_13, 0); }
		public TypeContext type() {
			return getRuleContext(TypeContext.class,0);
		}
		public Type3Context type3() {
			return getRuleContext(Type3Context.class,0);
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
		enterRule(_localctx, 164, RULE_type2);
		try {
			setState(971);
			_errHandler.sync(this);
			switch (_input.LA(1)) {
			case Surrogate_id_SYMB_4:
				enterOuterAlt(_localctx, 1);
				{
				setState(946);
				match(Surrogate_id_SYMB_4);
				setState(947);
				((Type2Context)_localctx).p_1_2 = listType();
				setState(948);
				match(Surrogate_id_SYMB_5);
				 ((Type2Context)_localctx).result =  new stella.Absyn.TypeTuple(((Type2Context)_localctx).p_1_2.result); 
				}
				break;
			case Surrogate_id_SYMB_50:
				enterOuterAlt(_localctx, 2);
				{
				setState(951);
				match(Surrogate_id_SYMB_50);
				setState(952);
				match(Surrogate_id_SYMB_4);
				setState(953);
				((Type2Context)_localctx).p_2_3 = listRecordFieldType();
				setState(954);
				match(Surrogate_id_SYMB_5);
				 ((Type2Context)_localctx).result =  new stella.Absyn.TypeRecord(((Type2Context)_localctx).p_2_3.result); 
				}
				break;
			case Surrogate_id_SYMB_58:
				enterOuterAlt(_localctx, 3);
				{
				setState(957);
				match(Surrogate_id_SYMB_58);
				setState(958);
				match(Surrogate_id_SYMB_10);
				setState(959);
				((Type2Context)_localctx).p_3_3 = listVariantFieldType();
				setState(960);
				match(Surrogate_id_SYMB_11);
				 ((Type2Context)_localctx).result =  new stella.Absyn.TypeVariant(((Type2Context)_localctx).p_3_3.result); 
				}
				break;
			case Surrogate_id_SYMB_12:
				enterOuterAlt(_localctx, 4);
				{
				setState(963);
				match(Surrogate_id_SYMB_12);
				setState(964);
				((Type2Context)_localctx).p_4_2 = type();
				setState(965);
				match(Surrogate_id_SYMB_13);
				 ((Type2Context)_localctx).result =  new stella.Absyn.TypeList(((Type2Context)_localctx).p_4_2.result); 
				}
				break;
			case Surrogate_id_SYMB_2:
			case Surrogate_id_SYMB_29:
			case Surrogate_id_SYMB_30:
			case Surrogate_id_SYMB_31:
			case StellaIdent:
				enterOuterAlt(_localctx, 5);
				{
				setState(968);
				((Type2Context)_localctx).p_5_1 = type3();
				 ((Type2Context)_localctx).result =  ((Type2Context)_localctx).p_5_1.result; 
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

	public static class Type3Context extends ParserRuleContext {
		public stella.Absyn.Type result;
		public Token p_4_1;
		public TypeContext p_5_2;
		public TerminalNode Surrogate_id_SYMB_29() { return getToken(stellaParser.Surrogate_id_SYMB_29, 0); }
		public TerminalNode Surrogate_id_SYMB_30() { return getToken(stellaParser.Surrogate_id_SYMB_30, 0); }
		public TerminalNode Surrogate_id_SYMB_31() { return getToken(stellaParser.Surrogate_id_SYMB_31, 0); }
		public TerminalNode StellaIdent() { return getToken(stellaParser.StellaIdent, 0); }
		public TerminalNode Surrogate_id_SYMB_2() { return getToken(stellaParser.Surrogate_id_SYMB_2, 0); }
		public TerminalNode Surrogate_id_SYMB_3() { return getToken(stellaParser.Surrogate_id_SYMB_3, 0); }
		public TypeContext type() {
			return getRuleContext(TypeContext.class,0);
		}
		public Type3Context(ParserRuleContext parent, int invokingState) {
			super(parent, invokingState);
		}
		@Override public int getRuleIndex() { return RULE_type3; }
		@Override
		public void enterRule(ParseTreeListener listener) {
			if ( listener instanceof stellaParserListener ) ((stellaParserListener)listener).enterType3(this);
		}
		@Override
		public void exitRule(ParseTreeListener listener) {
			if ( listener instanceof stellaParserListener ) ((stellaParserListener)listener).exitType3(this);
		}
	}

	public final Type3Context type3() throws RecognitionException {
		Type3Context _localctx = new Type3Context(_ctx, getState());
		enterRule(_localctx, 166, RULE_type3);
		try {
			setState(986);
			_errHandler.sync(this);
			switch (_input.LA(1)) {
			case Surrogate_id_SYMB_29:
				enterOuterAlt(_localctx, 1);
				{
				setState(973);
				match(Surrogate_id_SYMB_29);
				 ((Type3Context)_localctx).result =  new stella.Absyn.TypeBool(); 
				}
				break;
			case Surrogate_id_SYMB_30:
				enterOuterAlt(_localctx, 2);
				{
				setState(975);
				match(Surrogate_id_SYMB_30);
				 ((Type3Context)_localctx).result =  new stella.Absyn.TypeNat(); 
				}
				break;
			case Surrogate_id_SYMB_31:
				enterOuterAlt(_localctx, 3);
				{
				setState(977);
				match(Surrogate_id_SYMB_31);
				 ((Type3Context)_localctx).result =  new stella.Absyn.TypeUnit(); 
				}
				break;
			case StellaIdent:
				enterOuterAlt(_localctx, 4);
				{
				setState(979);
				((Type3Context)_localctx).p_4_1 = match(StellaIdent);
				 ((Type3Context)_localctx).result =  new stella.Absyn.TypeVar(((Type3Context)_localctx).p_4_1.getText()); 
				}
				break;
			case Surrogate_id_SYMB_2:
				enterOuterAlt(_localctx, 5);
				{
				setState(981);
				match(Surrogate_id_SYMB_2);
				setState(982);
				((Type3Context)_localctx).p_5_2 = type();
				setState(983);
				match(Surrogate_id_SYMB_3);
				 ((Type3Context)_localctx).result =  ((Type3Context)_localctx).p_5_2.result; 
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
		public TerminalNode Surrogate_id_SYMB_0() { return getToken(stellaParser.Surrogate_id_SYMB_0, 0); }
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
		enterRule(_localctx, 168, RULE_listType);
		try {
			setState(997);
			_errHandler.sync(this);
			switch ( getInterpreter().adaptivePredict(_input,35,_ctx) ) {
			case 1:
				enterOuterAlt(_localctx, 1);
				{
				 ((ListTypeContext)_localctx).result =  new stella.Absyn.ListType(); 
				}
				break;
			case 2:
				enterOuterAlt(_localctx, 2);
				{
				setState(989);
				((ListTypeContext)_localctx).p_2_1 = type();
				 ((ListTypeContext)_localctx).result =  new stella.Absyn.ListType(); _localctx.result.addLast(((ListTypeContext)_localctx).p_2_1.result); 
				}
				break;
			case 3:
				enterOuterAlt(_localctx, 3);
				{
				setState(992);
				((ListTypeContext)_localctx).p_3_1 = type();
				setState(993);
				match(Surrogate_id_SYMB_0);
				setState(994);
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

	public static class VariantFieldTypeContext extends ParserRuleContext {
		public stella.Absyn.VariantFieldType result;
		public Token p_1_1;
		public OptionalTypingContext p_1_2;
		public TerminalNode StellaIdent() { return getToken(stellaParser.StellaIdent, 0); }
		public OptionalTypingContext optionalTyping() {
			return getRuleContext(OptionalTypingContext.class,0);
		}
		public VariantFieldTypeContext(ParserRuleContext parent, int invokingState) {
			super(parent, invokingState);
		}
		@Override public int getRuleIndex() { return RULE_variantFieldType; }
		@Override
		public void enterRule(ParseTreeListener listener) {
			if ( listener instanceof stellaParserListener ) ((stellaParserListener)listener).enterVariantFieldType(this);
		}
		@Override
		public void exitRule(ParseTreeListener listener) {
			if ( listener instanceof stellaParserListener ) ((stellaParserListener)listener).exitVariantFieldType(this);
		}
	}

	public final VariantFieldTypeContext variantFieldType() throws RecognitionException {
		VariantFieldTypeContext _localctx = new VariantFieldTypeContext(_ctx, getState());
		enterRule(_localctx, 170, RULE_variantFieldType);
		try {
			enterOuterAlt(_localctx, 1);
			{
			setState(999);
			((VariantFieldTypeContext)_localctx).p_1_1 = match(StellaIdent);
			setState(1000);
			((VariantFieldTypeContext)_localctx).p_1_2 = optionalTyping();
			 ((VariantFieldTypeContext)_localctx).result =  new stella.Absyn.AVariantFieldType(((VariantFieldTypeContext)_localctx).p_1_1.getText(),((VariantFieldTypeContext)_localctx).p_1_2.result); 
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

	public static class ListVariantFieldTypeContext extends ParserRuleContext {
		public stella.Absyn.ListVariantFieldType result;
		public VariantFieldTypeContext p_2_1;
		public VariantFieldTypeContext p_3_1;
		public ListVariantFieldTypeContext p_3_3;
		public VariantFieldTypeContext variantFieldType() {
			return getRuleContext(VariantFieldTypeContext.class,0);
		}
		public TerminalNode Surrogate_id_SYMB_0() { return getToken(stellaParser.Surrogate_id_SYMB_0, 0); }
		public ListVariantFieldTypeContext listVariantFieldType() {
			return getRuleContext(ListVariantFieldTypeContext.class,0);
		}
		public ListVariantFieldTypeContext(ParserRuleContext parent, int invokingState) {
			super(parent, invokingState);
		}
		@Override public int getRuleIndex() { return RULE_listVariantFieldType; }
		@Override
		public void enterRule(ParseTreeListener listener) {
			if ( listener instanceof stellaParserListener ) ((stellaParserListener)listener).enterListVariantFieldType(this);
		}
		@Override
		public void exitRule(ParseTreeListener listener) {
			if ( listener instanceof stellaParserListener ) ((stellaParserListener)listener).exitListVariantFieldType(this);
		}
	}

	public final ListVariantFieldTypeContext listVariantFieldType() throws RecognitionException {
		ListVariantFieldTypeContext _localctx = new ListVariantFieldTypeContext(_ctx, getState());
		enterRule(_localctx, 172, RULE_listVariantFieldType);
		try {
			setState(1012);
			_errHandler.sync(this);
			switch ( getInterpreter().adaptivePredict(_input,36,_ctx) ) {
			case 1:
				enterOuterAlt(_localctx, 1);
				{
				 ((ListVariantFieldTypeContext)_localctx).result =  new stella.Absyn.ListVariantFieldType(); 
				}
				break;
			case 2:
				enterOuterAlt(_localctx, 2);
				{
				setState(1004);
				((ListVariantFieldTypeContext)_localctx).p_2_1 = variantFieldType();
				 ((ListVariantFieldTypeContext)_localctx).result =  new stella.Absyn.ListVariantFieldType(); _localctx.result.addLast(((ListVariantFieldTypeContext)_localctx).p_2_1.result); 
				}
				break;
			case 3:
				enterOuterAlt(_localctx, 3);
				{
				setState(1007);
				((ListVariantFieldTypeContext)_localctx).p_3_1 = variantFieldType();
				setState(1008);
				match(Surrogate_id_SYMB_0);
				setState(1009);
				((ListVariantFieldTypeContext)_localctx).p_3_3 = listVariantFieldType();
				 ((ListVariantFieldTypeContext)_localctx).result =  ((ListVariantFieldTypeContext)_localctx).p_3_3.result; _localctx.result.addFirst(((ListVariantFieldTypeContext)_localctx).p_3_1.result); 
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

	public static class RecordFieldTypeContext extends ParserRuleContext {
		public stella.Absyn.RecordFieldType result;
		public Token p_1_1;
		public TypeContext p_1_3;
		public TerminalNode Surrogate_id_SYMB_7() { return getToken(stellaParser.Surrogate_id_SYMB_7, 0); }
		public TerminalNode StellaIdent() { return getToken(stellaParser.StellaIdent, 0); }
		public TypeContext type() {
			return getRuleContext(TypeContext.class,0);
		}
		public RecordFieldTypeContext(ParserRuleContext parent, int invokingState) {
			super(parent, invokingState);
		}
		@Override public int getRuleIndex() { return RULE_recordFieldType; }
		@Override
		public void enterRule(ParseTreeListener listener) {
			if ( listener instanceof stellaParserListener ) ((stellaParserListener)listener).enterRecordFieldType(this);
		}
		@Override
		public void exitRule(ParseTreeListener listener) {
			if ( listener instanceof stellaParserListener ) ((stellaParserListener)listener).exitRecordFieldType(this);
		}
	}

	public final RecordFieldTypeContext recordFieldType() throws RecognitionException {
		RecordFieldTypeContext _localctx = new RecordFieldTypeContext(_ctx, getState());
		enterRule(_localctx, 174, RULE_recordFieldType);
		try {
			enterOuterAlt(_localctx, 1);
			{
			setState(1014);
			((RecordFieldTypeContext)_localctx).p_1_1 = match(StellaIdent);
			setState(1015);
			match(Surrogate_id_SYMB_7);
			setState(1016);
			((RecordFieldTypeContext)_localctx).p_1_3 = type();
			 ((RecordFieldTypeContext)_localctx).result =  new stella.Absyn.ARecordFieldType(((RecordFieldTypeContext)_localctx).p_1_1.getText(),((RecordFieldTypeContext)_localctx).p_1_3.result); 
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

	public static class ListRecordFieldTypeContext extends ParserRuleContext {
		public stella.Absyn.ListRecordFieldType result;
		public RecordFieldTypeContext p_2_1;
		public RecordFieldTypeContext p_3_1;
		public ListRecordFieldTypeContext p_3_3;
		public RecordFieldTypeContext recordFieldType() {
			return getRuleContext(RecordFieldTypeContext.class,0);
		}
		public TerminalNode Surrogate_id_SYMB_0() { return getToken(stellaParser.Surrogate_id_SYMB_0, 0); }
		public ListRecordFieldTypeContext listRecordFieldType() {
			return getRuleContext(ListRecordFieldTypeContext.class,0);
		}
		public ListRecordFieldTypeContext(ParserRuleContext parent, int invokingState) {
			super(parent, invokingState);
		}
		@Override public int getRuleIndex() { return RULE_listRecordFieldType; }
		@Override
		public void enterRule(ParseTreeListener listener) {
			if ( listener instanceof stellaParserListener ) ((stellaParserListener)listener).enterListRecordFieldType(this);
		}
		@Override
		public void exitRule(ParseTreeListener listener) {
			if ( listener instanceof stellaParserListener ) ((stellaParserListener)listener).exitListRecordFieldType(this);
		}
	}

	public final ListRecordFieldTypeContext listRecordFieldType() throws RecognitionException {
		ListRecordFieldTypeContext _localctx = new ListRecordFieldTypeContext(_ctx, getState());
		enterRule(_localctx, 176, RULE_listRecordFieldType);
		try {
			setState(1028);
			_errHandler.sync(this);
			switch ( getInterpreter().adaptivePredict(_input,37,_ctx) ) {
			case 1:
				enterOuterAlt(_localctx, 1);
				{
				 ((ListRecordFieldTypeContext)_localctx).result =  new stella.Absyn.ListRecordFieldType(); 
				}
				break;
			case 2:
				enterOuterAlt(_localctx, 2);
				{
				setState(1020);
				((ListRecordFieldTypeContext)_localctx).p_2_1 = recordFieldType();
				 ((ListRecordFieldTypeContext)_localctx).result =  new stella.Absyn.ListRecordFieldType(); _localctx.result.addLast(((ListRecordFieldTypeContext)_localctx).p_2_1.result); 
				}
				break;
			case 3:
				enterOuterAlt(_localctx, 3);
				{
				setState(1023);
				((ListRecordFieldTypeContext)_localctx).p_3_1 = recordFieldType();
				setState(1024);
				match(Surrogate_id_SYMB_0);
				setState(1025);
				((ListRecordFieldTypeContext)_localctx).p_3_3 = listRecordFieldType();
				 ((ListRecordFieldTypeContext)_localctx).result =  ((ListRecordFieldTypeContext)_localctx).p_3_3.result; _localctx.result.addFirst(((ListRecordFieldTypeContext)_localctx).p_3_1.result); 
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
		enterRule(_localctx, 178, RULE_typing);
		try {
			enterOuterAlt(_localctx, 1);
			{
			setState(1030);
			((TypingContext)_localctx).p_1_1 = expr();
			setState(1031);
			match(Surrogate_id_SYMB_7);
			setState(1032);
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
		case 50:
			return listExtension_sempred((ListExtensionContext)_localctx, predIndex);
		case 52:
			return listDecl_sempred((ListDeclContext)_localctx, predIndex);
		case 54:
			return listLocalDecl_sempred((ListLocalDeclContext)_localctx, predIndex);
		case 56:
			return listAnnotation_sempred((ListAnnotationContext)_localctx, predIndex);
		case 75:
			return expr2_sempred((Expr2Context)_localctx, predIndex);
		case 76:
			return expr3_sempred((Expr3Context)_localctx, predIndex);
		case 77:
			return expr4_sempred((Expr4Context)_localctx, predIndex);
		case 79:
			return expr6_sempred((Expr6Context)_localctx, predIndex);
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
	private boolean expr2_sempred(Expr2Context _localctx, int predIndex) {
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
	private boolean expr3_sempred(Expr3Context _localctx, int predIndex) {
		switch (predIndex) {
		case 7:
			return precpred(_ctx, 3);
		case 8:
			return precpred(_ctx, 2);
		}
		return true;
	}
	private boolean expr4_sempred(Expr4Context _localctx, int predIndex) {
		switch (predIndex) {
		case 9:
			return precpred(_ctx, 2);
		}
		return true;
	}
	private boolean expr6_sempred(Expr6Context _localctx, int predIndex) {
		switch (predIndex) {
		case 10:
			return precpred(_ctx, 7);
		case 11:
			return precpred(_ctx, 6);
		}
		return true;
	}

	public static final String _serializedATN =
		"\3\u608b\ua72a\u8133\ub9ed\u417c\u3be7\u7786\u5964\3F\u040e\4\2\t\2\4"+
		"\3\t\3\4\4\t\4\4\5\t\5\4\6\t\6\4\7\t\7\4\b\t\b\4\t\t\t\4\n\t\n\4\13\t"+
		"\13\4\f\t\f\4\r\t\r\4\16\t\16\4\17\t\17\4\20\t\20\4\21\t\21\4\22\t\22"+
		"\4\23\t\23\4\24\t\24\4\25\t\25\4\26\t\26\4\27\t\27\4\30\t\30\4\31\t\31"+
		"\4\32\t\32\4\33\t\33\4\34\t\34\4\35\t\35\4\36\t\36\4\37\t\37\4 \t \4!"+
		"\t!\4\"\t\"\4#\t#\4$\t$\4%\t%\4&\t&\4\'\t\'\4(\t(\4)\t)\4*\t*\4+\t+\4"+
		",\t,\4-\t-\4.\t.\4/\t/\4\60\t\60\4\61\t\61\4\62\t\62\4\63\t\63\4\64\t"+
		"\64\4\65\t\65\4\66\t\66\4\67\t\67\48\t8\49\t9\4:\t:\4;\t;\4<\t<\4=\t="+
		"\4>\t>\4?\t?\4@\t@\4A\tA\4B\tB\4C\tC\4D\tD\4E\tE\4F\tF\4G\tG\4H\tH\4I"+
		"\tI\4J\tJ\4K\tK\4L\tL\4M\tM\4N\tN\4O\tO\4P\tP\4Q\tQ\4R\tR\4S\tS\4T\tT"+
		"\4U\tU\4V\tV\4W\tW\4X\tX\4Y\tY\4Z\tZ\4[\t[\3\2\3\2\3\2\3\2\3\3\3\3\3\3"+
		"\3\3\3\4\3\4\3\4\3\4\3\5\3\5\3\5\3\5\3\6\3\6\3\6\3\6\3\7\3\7\3\7\3\7\3"+
		"\b\3\b\3\b\3\b\3\t\3\t\3\t\3\t\3\n\3\n\3\n\3\n\3\13\3\13\3\13\3\13\3\f"+
		"\3\f\3\f\3\f\3\r\3\r\3\r\3\r\3\16\3\16\3\16\3\16\3\17\3\17\3\17\3\17\3"+
		"\20\3\20\3\20\3\20\3\21\3\21\3\21\3\21\3\22\3\22\3\22\3\22\3\23\3\23\3"+
		"\23\3\23\3\24\3\24\3\24\3\24\3\25\3\25\3\25\3\25\3\26\3\26\3\26\3\26\3"+
		"\27\3\27\3\27\3\27\3\30\3\30\3\30\3\30\3\31\3\31\3\31\3\31\3\32\3\32\3"+
		"\32\3\32\3\33\3\33\3\33\3\33\3\34\3\34\3\34\3\34\3\35\3\35\3\35\3\35\3"+
		"\36\3\36\3\36\3\36\3\37\3\37\3\37\3\37\3 \3 \3 \3 \3!\3!\3!\3!\3\"\3\""+
		"\3\"\3\"\3#\3#\3#\3#\3$\3$\3$\3$\3%\3%\3%\3%\3&\3&\3&\3&\3\'\3\'\3\'\3"+
		"\'\3(\3(\3(\3(\3)\3)\3)\3)\3*\3*\3*\3*\3+\3+\3+\3+\3,\3,\3,\3,\3-\3-\3"+
		"-\3-\3.\3.\3.\3.\3/\3/\3/\3/\3/\3/\3/\3/\5/\u0173\n/\3\60\3\60\3\60\3"+
		"\60\3\60\3\61\3\61\3\61\3\61\3\61\3\62\3\62\3\62\3\62\3\62\3\63\3\63\3"+
		"\63\3\63\3\63\3\63\3\63\3\63\5\63\u018c\n\63\3\64\3\64\3\64\3\64\3\64"+
		"\3\64\3\64\3\64\7\64\u0196\n\64\f\64\16\64\u0199\13\64\3\65\3\65\3\65"+
		"\3\65\3\65\3\65\3\65\3\65\3\65\3\65\3\65\3\65\3\65\3\65\3\65\3\65\3\65"+
		"\3\65\3\65\3\65\3\65\3\65\5\65\u01b1\n\65\3\66\3\66\3\66\3\66\3\66\3\66"+
		"\3\66\7\66\u01ba\n\66\f\66\16\66\u01bd\13\66\3\67\3\67\3\67\38\38\38\3"+
		"8\38\38\38\38\78\u01ca\n8\f8\168\u01cd\138\39\39\39\3:\3:\3:\3:\3:\3:"+
		"\3:\7:\u01d9\n:\f:\16:\u01dc\13:\3;\3;\3;\3;\3;\3<\3<\3<\3<\3<\3<\3<\3"+
		"<\3<\5<\u01ec\n<\3=\3=\3=\3=\3=\5=\u01f3\n=\3>\3>\3>\3>\3>\5>\u01fa\n"+
		">\3?\3?\3?\3?\3?\3?\3?\3?\3?\3?\3?\3?\3?\3?\3?\3?\3?\3?\3?\5?\u020f\n"+
		"?\3@\3@\3@\3@\3@\3@\3@\3@\3@\5@\u021a\n@\3A\3A\3A\3A\3A\3B\3B\3B\3B\3"+
		"B\3B\3B\3B\3B\5B\u022a\nB\3C\3C\3C\3C\3C\5C\u0231\nC\3D\3D\3D\3D\3D\5"+
		"D\u0238\nD\3E\3E\3E\3E\3E\5E\u023f\nE\3F\3F\3F\3F\3F\3F\3F\3F\3F\3F\3"+
		"F\3F\3F\3F\3F\3F\3F\3F\3F\3F\3F\3F\3F\3F\3F\3F\3F\3F\3F\3F\3F\3F\3F\3"+
		"F\3F\3F\3F\3F\3F\3F\3F\3F\3F\3F\3F\3F\3F\3F\3F\5F\u0272\nF\3G\3G\3G\3"+
		"G\3G\3G\3G\3G\3G\5G\u027d\nG\3H\3H\3H\3H\3H\3I\3I\3I\3I\3I\3I\3I\3I\3"+
		"I\5I\u028d\nI\3J\3J\3J\3J\3J\3K\3K\3K\3K\3K\3K\3K\3K\3K\5K\u029d\nK\3"+
		"L\3L\3L\3L\3L\3L\3L\3L\3L\3L\3L\3L\3L\3L\3L\3L\3L\3L\3L\3L\3L\3L\3L\3"+
		"L\3L\3L\3L\3L\3L\3L\3L\3L\3L\5L\u02c0\nL\3M\3M\3M\3M\3M\3M\3M\3M\3M\3"+
		"M\3M\3M\3M\3M\3M\3M\3M\3M\3M\3M\3M\3M\3M\3M\3M\3M\3M\3M\3M\3M\3M\3M\3"+
		"M\3M\3M\3M\3M\3M\3M\3M\3M\3M\3M\3M\5M\u02ee\nM\3M\3M\3M\3M\3M\3M\3M\3"+
		"M\3M\3M\3M\3M\3M\3M\3M\7M\u02ff\nM\fM\16M\u0302\13M\3N\3N\3N\3N\3N\3N"+
		"\3N\3N\3N\3N\3N\3N\3N\3N\7N\u0312\nN\fN\16N\u0315\13N\3O\3O\3O\3O\3O\3"+
		"O\3O\3O\3O\3O\7O\u0321\nO\fO\16O\u0324\13O\3P\3P\3P\3P\3P\3P\3P\3P\3P"+
		"\3P\3P\3P\3P\3P\3P\3P\3P\3P\3P\3P\3P\3P\3P\3P\3P\3P\3P\3P\3P\3P\3P\3P"+
		"\3P\3P\3P\3P\3P\3P\3P\3P\3P\3P\3P\3P\3P\3P\3P\3P\3P\3P\3P\3P\3P\3P\3P"+
		"\3P\3P\3P\3P\3P\3P\3P\3P\3P\3P\3P\3P\3P\3P\3P\3P\3P\3P\3P\3P\3P\3P\3P"+
		"\3P\3P\3P\3P\3P\5P\u0379\nP\3Q\3Q\3Q\3Q\3Q\3Q\3Q\3Q\3Q\3Q\3Q\3Q\3Q\3Q"+
		"\5Q\u0389\nQ\3Q\3Q\3Q\3Q\3Q\3Q\3Q\3Q\7Q\u0393\nQ\fQ\16Q\u0396\13Q\3R\3"+
		"R\3R\3R\3R\3R\3R\3R\3R\3R\3R\3R\3R\3R\3R\3R\3R\5R\u03a9\nR\3S\3S\3S\3"+
		"S\3S\3S\3S\3S\5S\u03b3\nS\3T\3T\3T\3T\3T\3T\3T\3T\3T\3T\3T\3T\3T\3T\3"+
		"T\3T\3T\3T\3T\3T\3T\3T\3T\3T\3T\5T\u03ce\nT\3U\3U\3U\3U\3U\3U\3U\3U\3"+
		"U\3U\3U\3U\3U\5U\u03dd\nU\3V\3V\3V\3V\3V\3V\3V\3V\3V\5V\u03e8\nV\3W\3"+
		"W\3W\3W\3X\3X\3X\3X\3X\3X\3X\3X\3X\5X\u03f7\nX\3Y\3Y\3Y\3Y\3Y\3Z\3Z\3"+
		"Z\3Z\3Z\3Z\3Z\3Z\3Z\5Z\u0407\nZ\3[\3[\3[\3[\3[\3[\2\nfjnr\u0098\u009a"+
		"\u009c\u00a0\\\2\4\6\b\n\f\16\20\22\24\26\30\32\34\36 \"$&(*,.\60\62\64"+
		"\668:<>@BDFHJLNPRTVXZ\\^`bdfhjlnprtvxz|~\u0080\u0082\u0084\u0086\u0088"+
		"\u008a\u008c\u008e\u0090\u0092\u0094\u0096\u0098\u009a\u009c\u009e\u00a0"+
		"\u00a2\u00a4\u00a6\u00a8\u00aa\u00ac\u00ae\u00b0\u00b2\u00b4\2\2\2\u040e"+
		"\2\u00b6\3\2\2\2\4\u00ba\3\2\2\2\6\u00be\3\2\2\2\b\u00c2\3\2\2\2\n\u00c6"+
		"\3\2\2\2\f\u00ca\3\2\2\2\16\u00ce\3\2\2\2\20\u00d2\3\2\2\2\22\u00d6\3"+
		"\2\2\2\24\u00da\3\2\2\2\26\u00de\3\2\2\2\30\u00e2\3\2\2\2\32\u00e6\3\2"+
		"\2\2\34\u00ea\3\2\2\2\36\u00ee\3\2\2\2 \u00f2\3\2\2\2\"\u00f6\3\2\2\2"+
		"$\u00fa\3\2\2\2&\u00fe\3\2\2\2(\u0102\3\2\2\2*\u0106\3\2\2\2,\u010a\3"+
		"\2\2\2.\u010e\3\2\2\2\60\u0112\3\2\2\2\62\u0116\3\2\2\2\64\u011a\3\2\2"+
		"\2\66\u011e\3\2\2\28\u0122\3\2\2\2:\u0126\3\2\2\2<\u012a\3\2\2\2>\u012e"+
		"\3\2\2\2@\u0132\3\2\2\2B\u0136\3\2\2\2D\u013a\3\2\2\2F\u013e\3\2\2\2H"+
		"\u0142\3\2\2\2J\u0146\3\2\2\2L\u014a\3\2\2\2N\u014e\3\2\2\2P\u0152\3\2"+
		"\2\2R\u0156\3\2\2\2T\u015a\3\2\2\2V\u015e\3\2\2\2X\u0162\3\2\2\2Z\u0166"+
		"\3\2\2\2\\\u0172\3\2\2\2^\u0174\3\2\2\2`\u0179\3\2\2\2b\u017e\3\2\2\2"+
		"d\u018b\3\2\2\2f\u018d\3\2\2\2h\u01b0\3\2\2\2j\u01b2\3\2\2\2l\u01be\3"+
		"\2\2\2n\u01c1\3\2\2\2p\u01ce\3\2\2\2r\u01d1\3\2\2\2t\u01dd\3\2\2\2v\u01eb"+
		"\3\2\2\2x\u01f2\3\2\2\2z\u01f9\3\2\2\2|\u020e\3\2\2\2~\u0219\3\2\2\2\u0080"+
		"\u021b\3\2\2\2\u0082\u0229\3\2\2\2\u0084\u0230\3\2\2\2\u0086\u0237\3\2"+
		"\2\2\u0088\u023e\3\2\2\2\u008a\u0271\3\2\2\2\u008c\u027c\3\2\2\2\u008e"+
		"\u027e\3\2\2\2\u0090\u028c\3\2\2\2\u0092\u028e\3\2\2\2\u0094\u029c\3\2"+
		"\2\2\u0096\u02bf\3\2\2\2\u0098\u02ed\3\2\2\2\u009a\u0303\3\2\2\2\u009c"+
		"\u0316\3\2\2\2\u009e\u0378\3\2\2\2\u00a0\u0388\3\2\2\2\u00a2\u03a8\3\2"+
		"\2\2\u00a4\u03b2\3\2\2\2\u00a6\u03cd\3\2\2\2\u00a8\u03dc\3\2\2\2\u00aa"+
		"\u03e7\3\2\2\2\u00ac\u03e9\3\2\2\2\u00ae\u03f6\3\2\2\2\u00b0\u03f8\3\2"+
		"\2\2\u00b2\u0406\3\2\2\2\u00b4\u0408\3\2\2\2\u00b6\u00b7\5\\/\2\u00b7"+
		"\u00b8\7\2\2\3\u00b8\u00b9\b\2\1\2\u00b9\3\3\2\2\2\u00ba\u00bb\5^\60\2"+
		"\u00bb\u00bc\7\2\2\3\u00bc\u00bd\b\3\1\2\u00bd\5\3\2\2\2\u00be\u00bf\5"+
		"`\61\2\u00bf\u00c0\7\2\2\3\u00c0\u00c1\b\4\1\2\u00c1\7\3\2\2\2\u00c2\u00c3"+
		"\5b\62\2\u00c3\u00c4\7\2\2\3\u00c4\u00c5\b\5\1\2\u00c5\t\3\2\2\2\u00c6"+
		"\u00c7\5d\63\2\u00c7\u00c8\7\2\2\3\u00c8\u00c9\b\6\1\2\u00c9\13\3\2\2"+
		"\2\u00ca\u00cb\5f\64\2\u00cb\u00cc\7\2\2\3\u00cc\u00cd\b\7\1\2\u00cd\r"+
		"\3\2\2\2\u00ce\u00cf\5h\65\2\u00cf\u00d0\7\2\2\3\u00d0\u00d1\b\b\1\2\u00d1"+
		"\17\3\2\2\2\u00d2\u00d3\5j\66\2\u00d3\u00d4\7\2\2\3\u00d4\u00d5\b\t\1"+
		"\2\u00d5\21\3\2\2\2\u00d6\u00d7\5l\67\2\u00d7\u00d8\7\2\2\3\u00d8\u00d9"+
		"\b\n\1\2\u00d9\23\3\2\2\2\u00da\u00db\5n8\2\u00db\u00dc\7\2\2\3\u00dc"+
		"\u00dd\b\13\1\2\u00dd\25\3\2\2\2\u00de\u00df\5p9\2\u00df\u00e0\7\2\2\3"+
		"\u00e0\u00e1\b\f\1\2\u00e1\27\3\2\2\2\u00e2\u00e3\5r:\2\u00e3\u00e4\7"+
		"\2\2\3\u00e4\u00e5\b\r\1\2\u00e5\31\3\2\2\2\u00e6\u00e7\5t;\2\u00e7\u00e8"+
		"\7\2\2\3\u00e8\u00e9\b\16\1\2\u00e9\33\3\2\2\2\u00ea\u00eb\5v<\2\u00eb"+
		"\u00ec\7\2\2\3\u00ec\u00ed\b\17\1\2\u00ed\35\3\2\2\2\u00ee\u00ef\5x=\2"+
		"\u00ef\u00f0\7\2\2\3\u00f0\u00f1\b\20\1\2\u00f1\37\3\2\2\2\u00f2\u00f3"+
		"\5z>\2\u00f3\u00f4\7\2\2\3\u00f4\u00f5\b\21\1\2\u00f5!\3\2\2\2\u00f6\u00f7"+
		"\5|?\2\u00f7\u00f8\7\2\2\3\u00f8\u00f9\b\22\1\2\u00f9#\3\2\2\2\u00fa\u00fb"+
		"\5~@\2\u00fb\u00fc\7\2\2\3\u00fc\u00fd\b\23\1\2\u00fd%\3\2\2\2\u00fe\u00ff"+
		"\5\u0080A\2\u00ff\u0100\7\2\2\3\u0100\u0101\b\24\1\2\u0101\'\3\2\2\2\u0102"+
		"\u0103\5\u0082B\2\u0103\u0104\7\2\2\3\u0104\u0105\b\25\1\2\u0105)\3\2"+
		"\2\2\u0106\u0107\5\u0084C\2\u0107\u0108\7\2\2\3\u0108\u0109\b\26\1\2\u0109"+
		"+\3\2\2\2\u010a\u010b\5\u0086D\2\u010b\u010c\7\2\2\3\u010c\u010d\b\27"+
		"\1\2\u010d-\3\2\2\2\u010e\u010f\5\u0088E\2\u010f\u0110\7\2\2\3\u0110\u0111"+
		"\b\30\1\2\u0111/\3\2\2\2\u0112\u0113\5\u008aF\2\u0113\u0114\7\2\2\3\u0114"+
		"\u0115\b\31\1\2\u0115\61\3\2\2\2\u0116\u0117\5\u008cG\2\u0117\u0118\7"+
		"\2\2\3\u0118\u0119\b\32\1\2\u0119\63\3\2\2\2\u011a\u011b\5\u008eH\2\u011b"+
		"\u011c\7\2\2\3\u011c\u011d\b\33\1\2\u011d\65\3\2\2\2\u011e\u011f\5\u0090"+
		"I\2\u011f\u0120\7\2\2\3\u0120\u0121\b\34\1\2\u0121\67\3\2\2\2\u0122\u0123"+
		"\5\u0092J\2\u0123\u0124\7\2\2\3\u0124\u0125\b\35\1\2\u01259\3\2\2\2\u0126"+
		"\u0127\5\u0094K\2\u0127\u0128\7\2\2\3\u0128\u0129\b\36\1\2\u0129;\3\2"+
		"\2\2\u012a\u012b\5\u0096L\2\u012b\u012c\7\2\2\3\u012c\u012d\b\37\1\2\u012d"+
		"=\3\2\2\2\u012e\u012f\5\u0098M\2\u012f\u0130\7\2\2\3\u0130\u0131\b \1"+
		"\2\u0131?\3\2\2\2\u0132\u0133\5\u009aN\2\u0133\u0134\7\2\2\3\u0134\u0135"+
		"\b!\1\2\u0135A\3\2\2\2\u0136\u0137\5\u009cO\2\u0137\u0138\7\2\2\3\u0138"+
		"\u0139\b\"\1\2\u0139C\3\2\2\2\u013a\u013b\5\u009eP\2\u013b\u013c\7\2\2"+
		"\3\u013c\u013d\b#\1\2\u013dE\3\2\2\2\u013e\u013f\5\u00a0Q\2\u013f\u0140"+
		"\7\2\2\3\u0140\u0141\b$\1\2\u0141G\3\2\2\2\u0142\u0143\5\u00a2R\2\u0143"+
		"\u0144\7\2\2\3\u0144\u0145\b%\1\2\u0145I\3\2\2\2\u0146\u0147\5\u00a4S"+
		"\2\u0147\u0148\7\2\2\3\u0148\u0149\b&\1\2\u0149K\3\2\2\2\u014a\u014b\5"+
		"\u00a6T\2\u014b\u014c\7\2\2\3\u014c\u014d\b\'\1\2\u014dM\3\2\2\2\u014e"+
		"\u014f\5\u00a8U\2\u014f\u0150\7\2\2\3\u0150\u0151\b(\1\2\u0151O\3\2\2"+
		"\2\u0152\u0153\5\u00aaV\2\u0153\u0154\7\2\2\3\u0154\u0155\b)\1\2\u0155"+
		"Q\3\2\2\2\u0156\u0157\5\u00acW\2\u0157\u0158\7\2\2\3\u0158\u0159\b*\1"+
		"\2\u0159S\3\2\2\2\u015a\u015b\5\u00aeX\2\u015b\u015c\7\2\2\3\u015c\u015d"+
		"\b+\1\2\u015dU\3\2\2\2\u015e\u015f\5\u00b0Y\2\u015f\u0160\7\2\2\3\u0160"+
		"\u0161\b,\1\2\u0161W\3\2\2\2\u0162\u0163\5\u00b2Z\2\u0163\u0164\7\2\2"+
		"\3\u0164\u0165\b-\1\2\u0165Y\3\2\2\2\u0166\u0167\5\u00b4[\2\u0167\u0168"+
		"\7\2\2\3\u0168\u0169\b.\1\2\u0169[\3\2\2\2\u016a\u0173\b/\1\2\u016b\u016c"+
		"\7B\2\2\u016c\u0173\b/\1\2\u016d\u016e\7B\2\2\u016e\u016f\7\3\2\2\u016f"+
		"\u0170\5\\/\2\u0170\u0171\b/\1\2\u0171\u0173\3\2\2\2\u0172\u016a\3\2\2"+
		"\2\u0172\u016b\3\2\2\2\u0172\u016d\3\2\2\2\u0173]\3\2\2\2\u0174\u0175"+
		"\5`\61\2\u0175\u0176\5f\64\2\u0176\u0177\5j\66\2\u0177\u0178\b\60\1\2"+
		"\u0178_\3\2\2\2\u0179\u017a\7\60\2\2\u017a\u017b\7&\2\2\u017b\u017c\7"+
		"\4\2\2\u017c\u017d\b\61\1\2\u017da\3\2\2\2\u017e\u017f\7(\2\2\u017f\u0180"+
		"\7>\2\2\u0180\u0181\5d\63\2\u0181\u0182\b\62\1\2\u0182c\3\2\2\2\u0183"+
		"\u018c\b\63\1\2\u0184\u0185\7C\2\2\u0185\u018c\b\63\1\2\u0186\u0187\7"+
		"C\2\2\u0187\u0188\7\3\2\2\u0188\u0189\5d\63\2\u0189\u018a\b\63\1\2\u018a"+
		"\u018c\3\2\2\2\u018b\u0183\3\2\2\2\u018b\u0184\3\2\2\2\u018b\u0186\3\2"+
		"\2\2\u018ce\3\2\2\2\u018d\u018e\b\64\1\2\u018e\u018f\b\64\1\2\u018f\u0197"+
		"\3\2\2\2\u0190\u0191\f\3\2\2\u0191\u0192\5b\62\2\u0192\u0193\7\4\2\2\u0193"+
		"\u0194\b\64\1\2\u0194\u0196\3\2\2\2\u0195\u0190\3\2\2\2\u0196\u0199\3"+
		"\2\2\2\u0197\u0195\3\2\2\2\u0197\u0198\3\2\2\2\u0198g\3\2\2\2\u0199\u0197"+
		"\3\2\2\2\u019a\u019b\5r:\2\u019b\u019c\7+\2\2\u019c\u019d\7B\2\2\u019d"+
		"\u019e\7\5\2\2\u019e\u019f\5v<\2\u019f\u01a0\7\6\2\2\u01a0\u01a1\5x=\2"+
		"\u01a1\u01a2\5z>\2\u01a2\u01a3\7\7\2\2\u01a3\u01a4\5j\66\2\u01a4\u01a5"+
		"\7\66\2\2\u01a5\u01a6\5|?\2\u01a6\u01a7\7\4\2\2\u01a7\u01a8\7\b\2\2\u01a8"+
		"\u01a9\b\65\1\2\u01a9\u01b1\3\2\2\2\u01aa\u01ab\7;\2\2\u01ab\u01ac\7B"+
		"\2\2\u01ac\u01ad\7\t\2\2\u01ad\u01ae\5\u00a2R\2\u01ae\u01af\b\65\1\2\u01af"+
		"\u01b1\3\2\2\2\u01b0\u019a\3\2\2\2\u01b0\u01aa\3\2\2\2\u01b1i\3\2\2\2"+
		"\u01b2\u01b3\b\66\1\2\u01b3\u01b4\b\66\1\2\u01b4\u01bb\3\2\2\2\u01b5\u01b6"+
		"\f\3\2\2\u01b6\u01b7\5h\65\2\u01b7\u01b8\b\66\1\2\u01b8\u01ba\3\2\2\2"+
		"\u01b9\u01b5\3\2\2\2\u01ba\u01bd\3\2\2\2\u01bb\u01b9\3\2\2\2\u01bb\u01bc"+
		"\3\2\2\2\u01bck\3\2\2\2\u01bd\u01bb\3\2\2\2\u01be\u01bf\5h\65\2\u01bf"+
		"\u01c0\b\67\1\2\u01c0m\3\2\2\2\u01c1\u01c2\b8\1\2\u01c2\u01c3\b8\1\2\u01c3"+
		"\u01cb\3\2\2\2\u01c4\u01c5\f\3\2\2\u01c5\u01c6\5l\67\2\u01c6\u01c7\7\4"+
		"\2\2\u01c7\u01c8\b8\1\2\u01c8\u01ca\3\2\2\2\u01c9\u01c4\3\2\2\2\u01ca"+
		"\u01cd\3\2\2\2\u01cb\u01c9\3\2\2\2\u01cb\u01cc\3\2\2\2\u01cco\3\2\2\2"+
		"\u01cd\u01cb\3\2\2\2\u01ce\u01cf\7/\2\2\u01cf\u01d0\b9\1\2\u01d0q\3\2"+
		"\2\2\u01d1\u01d2\b:\1\2\u01d2\u01d3\b:\1\2\u01d3\u01da\3\2\2\2\u01d4\u01d5"+
		"\f\3\2\2\u01d5\u01d6\5p9\2\u01d6\u01d7\b:\1\2\u01d7\u01d9\3\2\2\2\u01d8"+
		"\u01d4\3\2\2\2\u01d9\u01dc\3\2\2\2\u01da\u01d8\3\2\2\2\u01da\u01db\3\2"+
		"\2\2\u01dbs\3\2\2\2\u01dc\u01da\3\2\2\2\u01dd\u01de\7B\2\2\u01de\u01df"+
		"\7\n\2\2\u01df\u01e0\5\u00a2R\2\u01e0\u01e1\b;\1\2\u01e1u\3\2\2\2\u01e2"+
		"\u01ec\b<\1\2\u01e3\u01e4\5t;\2\u01e4\u01e5\b<\1\2\u01e5\u01ec\3\2\2\2"+
		"\u01e6\u01e7\5t;\2\u01e7\u01e8\7\3\2\2\u01e8\u01e9\5v<\2\u01e9\u01ea\b"+
		"<\1\2\u01ea\u01ec\3\2\2\2\u01eb\u01e2\3\2\2\2\u01eb\u01e3\3\2\2\2\u01eb"+
		"\u01e6\3\2\2\2\u01ecw\3\2\2\2\u01ed\u01f3\b=\1\2\u01ee\u01ef\7\13\2\2"+
		"\u01ef\u01f0\5\u00a2R\2\u01f0\u01f1\b=\1\2\u01f1\u01f3\3\2\2\2\u01f2\u01ed"+
		"\3\2\2\2\u01f2\u01ee\3\2\2\2\u01f3y\3\2\2\2\u01f4\u01fa\b>\1\2\u01f5\u01f6"+
		"\79\2\2\u01f6\u01f7\5\u00aaV\2\u01f7\u01f8\b>\1\2\u01f8\u01fa\3\2\2\2"+
		"\u01f9\u01f4\3\2\2\2\u01f9\u01f5\3\2\2\2\u01fa{\3\2\2\2\u01fb\u01fc\7"+
		"-\2\2\u01fc\u01fd\5|?\2\u01fd\u01fe\78\2\2\u01fe\u01ff\5|?\2\u01ff\u0200"+
		"\7\'\2\2\u0200\u0201\5|?\2\u0201\u0202\b?\1\2\u0202\u020f\3\2\2\2\u0203"+
		"\u0204\7\61\2\2\u0204\u0205\7B\2\2\u0205\u0206\7\t\2\2\u0206\u0207\5|"+
		"?\2\u0207\u0208\7.\2\2\u0208\u0209\5|?\2\u0209\u020a\b?\1\2\u020a\u020f"+
		"\3\2\2\2\u020b\u020c\5\u0096L\2\u020c\u020d\b?\1\2\u020d\u020f\3\2\2\2"+
		"\u020e\u01fb\3\2\2\2\u020e\u0203\3\2\2\2\u020e\u020b\3\2\2\2\u020f}\3"+
		"\2\2\2\u0210\u021a\b@\1\2\u0211\u0212\5|?\2\u0212\u0213\b@\1\2\u0213\u021a"+
		"\3\2\2\2\u0214\u0215\5|?\2\u0215\u0216\7\3\2\2\u0216\u0217\5~@\2\u0217"+
		"\u0218\b@\1\2\u0218\u021a\3\2\2\2\u0219\u0210\3\2\2\2\u0219\u0211\3\2"+
		"\2\2\u0219\u0214\3\2\2\2\u021a\177\3\2\2\2\u021b\u021c\5\u008aF\2\u021c"+
		"\u021d\7\f\2\2\u021d\u021e\5|?\2\u021e\u021f\bA\1\2\u021f\u0081\3\2\2"+
		"\2\u0220\u022a\bB\1\2\u0221\u0222\5\u0080A\2\u0222\u0223\bB\1\2\u0223"+
		"\u022a\3\2\2\2\u0224\u0225\5\u0080A\2\u0225\u0226\7\4\2\2\u0226\u0227"+
		"\5\u0082B\2\u0227\u0228\bB\1\2\u0228\u022a\3\2\2\2\u0229\u0220\3\2\2\2"+
		"\u0229\u0221\3\2\2\2\u0229\u0224\3\2\2\2\u022a\u0083\3\2\2\2\u022b\u0231"+
		"\bC\1\2\u022c\u022d\7\n\2\2\u022d\u022e\5\u00a2R\2\u022e\u022f\bC\1\2"+
		"\u022f\u0231\3\2\2\2\u0230\u022b\3\2\2\2\u0230\u022c\3\2\2\2\u0231\u0085"+
		"\3\2\2\2\u0232\u0238\bD\1\2\u0233\u0234\7\t\2\2\u0234\u0235\5\u008aF\2"+
		"\u0235\u0236\bD\1\2\u0236\u0238\3\2\2\2\u0237\u0232\3\2\2\2\u0237\u0233"+
		"\3\2\2\2\u0238\u0087\3\2\2\2\u0239\u023f\bE\1\2\u023a\u023b\7\t\2\2\u023b"+
		"\u023c\5|?\2\u023c\u023d\bE\1\2\u023d\u023f\3\2\2\2\u023e\u0239\3\2\2"+
		"\2\u023e\u023a\3\2\2\2\u023f\u0089\3\2\2\2\u0240\u0241\7\r\2\2\u0241\u0242"+
		"\7B\2\2\u0242\u0243\5\u0086D\2\u0243\u0244\7\16\2\2\u0244\u0245\bF\1\2"+
		"\u0245\u0272\3\2\2\2\u0246\u0247\7\7\2\2\u0247\u0248\5\u008cG\2\u0248"+
		"\u0249\7\b\2\2\u0249\u024a\bF\1\2\u024a\u0272\3\2\2\2\u024b\u024c\7\65"+
		"\2\2\u024c\u024d\7\7\2\2\u024d\u024e\5\u0090I\2\u024e\u024f\7\b\2\2\u024f"+
		"\u0250\bF\1\2\u0250\u0272\3\2\2\2\u0251\u0252\7\17\2\2\u0252\u0253\5\u008c"+
		"G\2\u0253\u0254\7\20\2\2\u0254\u0255\bF\1\2\u0255\u0272\3\2\2\2\u0256"+
		"\u0257\7%\2\2\u0257\u0258\7\5\2\2\u0258\u0259\5\u008aF\2\u0259\u025a\7"+
		"\3\2\2\u025a\u025b\5\u008aF\2\u025b\u025c\7\6\2\2\u025c\u025d\bF\1\2\u025d"+
		"\u0272\3\2\2\2\u025e\u025f\7)\2\2\u025f\u0272\bF\1\2\u0260\u0261\7:\2"+
		"\2\u0261\u0272\bF\1\2\u0262\u0263\7D\2\2\u0263\u0272\bF\1\2\u0264\u0265"+
		"\7\67\2\2\u0265\u0266\7\5\2\2\u0266\u0267\5\u008aF\2\u0267\u0268\7\6\2"+
		"\2\u0268\u0269\bF\1\2\u0269\u0272\3\2\2\2\u026a\u026b\7B\2\2\u026b\u0272"+
		"\bF\1\2\u026c\u026d\7\5\2\2\u026d\u026e\5\u008aF\2\u026e\u026f\7\6\2\2"+
		"\u026f\u0270\bF\1\2\u0270\u0272\3\2\2\2\u0271\u0240\3\2\2\2\u0271\u0246"+
		"\3\2\2\2\u0271\u024b\3\2\2\2\u0271\u0251\3\2\2\2\u0271\u0256\3\2\2\2\u0271"+
		"\u025e\3\2\2\2\u0271\u0260\3\2\2\2\u0271\u0262\3\2\2\2\u0271\u0264\3\2"+
		"\2\2\u0271\u026a\3\2\2\2\u0271\u026c\3\2\2\2\u0272\u008b\3\2\2\2\u0273"+
		"\u027d\bG\1\2\u0274\u0275\5\u008aF\2\u0275\u0276\bG\1\2\u0276\u027d\3"+
		"\2\2\2\u0277\u0278\5\u008aF\2\u0278\u0279\7\3\2\2\u0279\u027a\5\u008c"+
		"G\2\u027a\u027b\bG\1\2\u027b\u027d\3\2\2\2\u027c\u0273\3\2\2\2\u027c\u0274"+
		"\3\2\2\2\u027c\u0277\3\2\2\2\u027d\u008d\3\2\2\2\u027e\u027f\7B\2\2\u027f"+
		"\u0280\7\t\2\2\u0280\u0281\5\u008aF\2\u0281\u0282\bH\1\2\u0282\u008f\3"+
		"\2\2\2\u0283\u028d\bI\1\2\u0284\u0285\5\u008eH\2\u0285\u0286\bI\1\2\u0286"+
		"\u028d\3\2\2\2\u0287\u0288\5\u008eH\2\u0288\u0289\7\3\2\2\u0289\u028a"+
		"\5\u0090I\2\u028a\u028b\bI\1\2\u028b\u028d\3\2\2\2\u028c\u0283\3\2\2\2"+
		"\u028c\u0284\3\2\2\2\u028c\u0287\3\2\2\2\u028d\u0091\3\2\2\2\u028e\u028f"+
		"\7B\2\2\u028f\u0290\7\t\2\2\u0290\u0291\5|?\2\u0291\u0292\bJ\1\2\u0292"+
		"\u0093\3\2\2\2\u0293\u029d\bK\1\2\u0294\u0295\5\u0092J\2\u0295\u0296\b"+
		"K\1\2\u0296\u029d\3\2\2\2\u0297\u0298\5\u0092J\2\u0298\u0299\7\3\2\2\u0299"+
		"\u029a\5\u0094K\2\u029a\u029b\bK\1\2\u029b\u029d\3\2\2\2\u029c\u0293\3"+
		"\2\2\2\u029c\u0294\3\2\2\2\u029c\u0297\3\2\2\2\u029d\u0095\3\2\2\2\u029e"+
		"\u029f\5\u0098M\2\u029f\u02a0\7\21\2\2\u02a0\u02a1\5\u0098M\2\u02a1\u02a2"+
		"\bL\1\2\u02a2\u02c0\3\2\2\2\u02a3\u02a4\5\u0098M\2\u02a4\u02a5\7\22\2"+
		"\2\u02a5\u02a6\5\u0098M\2\u02a6\u02a7\bL\1\2\u02a7\u02c0\3\2\2\2\u02a8"+
		"\u02a9\5\u0098M\2\u02a9\u02aa\7\23\2\2\u02aa\u02ab\5\u0098M\2\u02ab\u02ac"+
		"\bL\1\2\u02ac\u02c0\3\2\2\2\u02ad\u02ae\5\u0098M\2\u02ae\u02af\7\24\2"+
		"\2\u02af\u02b0\5\u0098M\2\u02b0\u02b1\bL\1\2\u02b1\u02c0\3\2\2\2\u02b2"+
		"\u02b3\5\u0098M\2\u02b3\u02b4\7\25\2\2\u02b4\u02b5\5\u0098M\2\u02b5\u02b6"+
		"\bL\1\2\u02b6\u02c0\3\2\2\2\u02b7\u02b8\5\u0098M\2\u02b8\u02b9\7\26\2"+
		"\2\u02b9\u02ba\5\u0098M\2\u02ba\u02bb\bL\1\2\u02bb\u02c0\3\2\2\2\u02bc"+
		"\u02bd\5\u0098M\2\u02bd\u02be\bL\1\2\u02be\u02c0\3\2\2\2\u02bf\u029e\3"+
		"\2\2\2\u02bf\u02a3\3\2\2\2\u02bf\u02a8\3\2\2\2\u02bf\u02ad\3\2\2\2\u02bf"+
		"\u02b2\3\2\2\2\u02bf\u02b7\3\2\2\2\u02bf\u02bc\3\2\2\2\u02c0\u0097\3\2"+
		"\2\2\u02c1\u02c2\bM\1\2\u02c2\u02c3\7+\2\2\u02c3\u02c4\7\5\2\2\u02c4\u02c5"+
		"\5v<\2\u02c5\u02c6\7\6\2\2\u02c6\u02c7\7\7\2\2\u02c7\u02c8\7\66\2\2\u02c8"+
		"\u02c9\5|?\2\u02c9\u02ca\7\4\2\2\u02ca\u02cb\7\b\2\2\u02cb\u02cc\bM\1"+
		"\2\u02cc\u02ee\3\2\2\2\u02cd\u02ce\7\7\2\2\u02ce\u02cf\5~@\2\u02cf\u02d0"+
		"\7\b\2\2\u02d0\u02d1\bM\1\2\u02d1\u02ee\3\2\2\2\u02d2\u02d3\7\65\2\2\u02d3"+
		"\u02d4\7\7\2\2\u02d4\u02d5\5\u0094K\2\u02d5\u02d6\7\b\2\2\u02d6\u02d7"+
		"\bM\1\2\u02d7\u02ee\3\2\2\2\u02d8\u02d9\7\r\2\2\u02d9\u02da\7B\2\2\u02da"+
		"\u02db\5\u0088E\2\u02db\u02dc\7\16\2\2\u02dc\u02dd\bM\1\2\u02dd\u02ee"+
		"\3\2\2\2\u02de\u02df\7\62\2\2\u02df\u02e0\5\u0096L\2\u02e0\u02e1\7\7\2"+
		"\2\u02e1\u02e2\5\u0082B\2\u02e2\u02e3\7\b\2\2\u02e3\u02e4\bM\1\2\u02e4"+
		"\u02ee\3\2\2\2\u02e5\u02e6\7\17\2\2\u02e6\u02e7\5~@\2\u02e7\u02e8\7\20"+
		"\2\2\u02e8\u02e9\bM\1\2\u02e9\u02ee\3\2\2\2\u02ea\u02eb\5\u009aN\2\u02eb"+
		"\u02ec\bM\1\2\u02ec\u02ee\3\2\2\2\u02ed\u02c1\3\2\2\2\u02ed\u02cd\3\2"+
		"\2\2\u02ed\u02d2\3\2\2\2\u02ed\u02d8\3\2\2\2\u02ed\u02de\3\2\2\2\u02ed"+
		"\u02e5\3\2\2\2\u02ed\u02ea\3\2\2\2\u02ee\u0300\3\2\2\2\u02ef\u02f0\f\f"+
		"\2\2\u02f0\u02f1\7$\2\2\u02f1\u02f2\5\u00a2R\2\u02f2\u02f3\bM\1\2\u02f3"+
		"\u02ff\3\2\2\2\u02f4\u02f5\f\5\2\2\u02f5\u02f6\7\27\2\2\u02f6\u02f7\5"+
		"\u009aN\2\u02f7\u02f8\bM\1\2\u02f8\u02ff\3\2\2\2\u02f9\u02fa\f\4\2\2\u02fa"+
		"\u02fb\7\64\2\2\u02fb\u02fc\5\u009aN\2\u02fc\u02fd\bM\1\2\u02fd\u02ff"+
		"\3\2\2\2\u02fe\u02ef\3\2\2\2\u02fe\u02f4\3\2\2\2\u02fe\u02f9\3\2\2\2\u02ff"+
		"\u0302\3\2\2\2\u0300\u02fe\3\2\2\2\u0300\u0301\3\2\2\2\u0301\u0099\3\2"+
		"\2\2\u0302\u0300\3\2\2\2\u0303\u0304\bN\1\2\u0304\u0305\5\u009cO\2\u0305"+
		"\u0306\bN\1\2\u0306\u0313\3\2\2\2\u0307\u0308\f\5\2\2\u0308\u0309\7\30"+
		"\2\2\u0309\u030a\5\u009cO\2\u030a\u030b\bN\1\2\u030b\u0312\3\2\2\2\u030c"+
		"\u030d\f\4\2\2\u030d\u030e\7#\2\2\u030e\u030f\5\u009cO\2\u030f\u0310\b"+
		"N\1\2\u0310\u0312\3\2\2\2\u0311\u0307\3\2\2\2\u0311\u030c\3\2\2\2\u0312"+
		"\u0315\3\2\2\2\u0313\u0311\3\2\2\2\u0313\u0314\3\2\2\2\u0314\u009b\3\2"+
		"\2\2\u0315\u0313\3\2\2\2\u0316\u0317\bO\1\2\u0317\u0318\5\u009eP\2\u0318"+
		"\u0319\bO\1\2\u0319\u0322\3\2\2\2\u031a\u031b\f\4\2\2\u031b\u031c\7\5"+
		"\2\2\u031c\u031d\5~@\2\u031d\u031e\7\6\2\2\u031e\u031f\bO\1\2\u031f\u0321"+
		"\3\2\2\2\u0320\u031a\3\2\2\2\u0321\u0324\3\2\2\2\u0322\u0320\3\2\2\2\u0322"+
		"\u0323\3\2\2\2\u0323\u009d\3\2\2\2\u0324\u0322\3\2\2\2\u0325\u0326\7%"+
		"\2\2\u0326\u0327\7\5\2\2\u0327\u0328\5|?\2\u0328\u0329\7\3\2\2\u0329\u032a"+
		"\5|?\2\u032a\u032b\7\6\2\2\u032b\u032c\bP\1\2\u032c\u0379\3\2\2\2\u032d"+
		"\u032e\7\31\2\2\u032e\u032f\7\5\2\2\u032f\u0330\5|?\2\u0330\u0331\7\6"+
		"\2\2\u0331\u0332\bP\1\2\u0332\u0379\3\2\2\2\u0333\u0334\7\32\2\2\u0334"+
		"\u0335\7\5\2\2\u0335\u0336\5|?\2\u0336\u0337\7\6\2\2\u0337\u0338\bP\1"+
		"\2\u0338\u0379\3\2\2\2\u0339\u033a\7\33\2\2\u033a\u033b\7\5\2\2\u033b"+
		"\u033c\5|?\2\u033c\u033d\7\6\2\2\u033d\u033e\bP\1\2\u033e\u0379\3\2\2"+
		"\2\u033f\u0340\7\67\2\2\u0340\u0341\7\5\2\2\u0341\u0342\5|?\2\u0342\u0343"+
		"\7\6\2\2\u0343\u0344\bP\1\2\u0344\u0379\3\2\2\2\u0345\u0346\7\63\2\2\u0346"+
		"\u0347\7\5\2\2\u0347\u0348\5|?\2\u0348\u0349\7\6\2\2\u0349\u034a\bP\1"+
		"\2\u034a\u0379\3\2\2\2\u034b\u034c\7\34\2\2\u034c\u034d\7\5\2\2\u034d"+
		"\u034e\5|?\2\u034e\u034f\7\6\2\2\u034f\u0350\bP\1\2\u0350\u0379\3\2\2"+
		"\2\u0351\u0352\7\35\2\2\u0352\u0353\7\5\2\2\u0353\u0354\5|?\2\u0354\u0355"+
		"\7\6\2\2\u0355\u0356\bP\1\2\u0356\u0379\3\2\2\2\u0357\u0358\7*\2\2\u0358"+
		"\u0359\7\5\2\2\u0359\u035a\5|?\2\u035a\u035b\7\6\2\2\u035b\u035c\bP\1"+
		"\2\u035c\u0379\3\2\2\2\u035d\u035e\7\36\2\2\u035e\u035f\7\5\2\2\u035f"+
		"\u0360\5|?\2\u0360\u0361\7\3\2\2\u0361\u0362\5|?\2\u0362\u0363\7\3\2\2"+
		"\u0363\u0364\5|?\2\u0364\u0365\7\6\2\2\u0365\u0366\bP\1\2\u0366\u0379"+
		"\3\2\2\2\u0367\u0368\7,\2\2\u0368\u0369\7\17\2\2\u0369\u036a\5\u00a2R"+
		"\2\u036a\u036b\7\20\2\2\u036b\u036c\5\u00a0Q\2\u036c\u036d\bP\1\2\u036d"+
		"\u0379\3\2\2\2\u036e\u036f\7<\2\2\u036f\u0370\7\17\2\2\u0370\u0371\5\u00a2"+
		"R\2\u0371\u0372\7\20\2\2\u0372\u0373\5\u00a0Q\2\u0373\u0374\bP\1\2\u0374"+
		"\u0379\3\2\2\2\u0375\u0376\5\u00a0Q\2\u0376\u0377\bP\1\2\u0377\u0379\3"+
		"\2\2\2\u0378\u0325\3\2\2\2\u0378\u032d\3\2\2\2\u0378\u0333\3\2\2\2\u0378"+
		"\u0339\3\2\2\2\u0378\u033f\3\2\2\2\u0378\u0345\3\2\2\2\u0378\u034b\3\2"+
		"\2\2\u0378\u0351\3\2\2\2\u0378\u0357\3\2\2\2\u0378\u035d\3\2\2\2\u0378"+
		"\u0367\3\2\2\2\u0378\u036e\3\2\2\2\u0378\u0375\3\2\2\2\u0379\u009f\3\2"+
		"\2\2\u037a\u037b\bQ\1\2\u037b\u037c\7:\2\2\u037c\u0389\bQ\1\2\u037d\u037e"+
		"\7)\2\2\u037e\u0389\bQ\1\2\u037f\u0380\7D\2\2\u0380\u0389\bQ\1\2\u0381"+
		"\u0382\7B\2\2\u0382\u0389\bQ\1\2\u0383\u0384\7\5\2\2\u0384\u0385\5|?\2"+
		"\u0385\u0386\7\6\2\2\u0386\u0387\bQ\1\2\u0387\u0389\3\2\2\2\u0388\u037a"+
		"\3\2\2\2\u0388\u037d\3\2\2\2\u0388\u037f\3\2\2\2\u0388\u0381\3\2\2\2\u0388"+
		"\u0383\3\2\2\2\u0389\u0394\3\2\2\2\u038a\u038b\f\t\2\2\u038b\u038c\7\37"+
		"\2\2\u038c\u038d\7B\2\2\u038d\u0393\bQ\1\2\u038e\u038f\f\b\2\2\u038f\u0390"+
		"\7\37\2\2\u0390\u0391\7D\2\2\u0391\u0393\bQ\1\2\u0392\u038a\3\2\2\2\u0392"+
		"\u038e\3\2\2\2\u0393\u0396\3\2\2\2\u0394\u0392\3\2\2\2\u0394\u0395\3\2"+
		"\2\2\u0395\u00a1\3\2\2\2\u0396\u0394\3\2\2\2\u0397\u0398\7+\2\2\u0398"+
		"\u0399\7\5\2\2\u0399\u039a\5\u00aaV\2\u039a\u039b\7\6\2\2\u039b\u039c"+
		"\7\13\2\2\u039c\u039d\5\u00a2R\2\u039d\u039e\bR\1\2\u039e\u03a9\3\2\2"+
		"\2\u039f\u03a0\7?\2\2\u03a0\u03a1\7B\2\2\u03a1\u03a2\7\37\2\2\u03a2\u03a3"+
		"\5\u00a2R\2\u03a3\u03a4\bR\1\2\u03a4\u03a9\3\2\2\2\u03a5\u03a6\5\u00a4"+
		"S\2\u03a6\u03a7\bR\1\2\u03a7\u03a9\3\2\2\2\u03a8\u0397\3\2\2\2\u03a8\u039f"+
		"\3\2\2\2\u03a8\u03a5\3\2\2\2\u03a9\u00a3\3\2\2\2\u03aa\u03ab\5\u00a6T"+
		"\2\u03ab\u03ac\7\27\2\2\u03ac\u03ad\5\u00a6T\2\u03ad\u03ae\bS\1\2\u03ae"+
		"\u03b3\3\2\2\2\u03af\u03b0\5\u00a6T\2\u03b0\u03b1\bS\1\2\u03b1\u03b3\3"+
		"\2\2\2\u03b2\u03aa\3\2\2\2\u03b2\u03af\3\2\2\2\u03b3\u00a5\3\2\2\2\u03b4"+
		"\u03b5\7\7\2\2\u03b5\u03b6\5\u00aaV\2\u03b6\u03b7\7\b\2\2\u03b7\u03b8"+
		"\bT\1\2\u03b8\u03ce\3\2\2\2\u03b9\u03ba\7\65\2\2\u03ba\u03bb\7\7\2\2\u03bb"+
		"\u03bc\5\u00b2Z\2\u03bc\u03bd\7\b\2\2\u03bd\u03be\bT\1\2\u03be\u03ce\3"+
		"\2\2\2\u03bf\u03c0\7=\2\2\u03c0\u03c1\7\r\2\2\u03c1\u03c2\5\u00aeX\2\u03c2"+
		"\u03c3\7\16\2\2\u03c3\u03c4\bT\1\2\u03c4\u03ce\3\2\2\2\u03c5\u03c6\7\17"+
		"\2\2\u03c6\u03c7\5\u00a2R\2\u03c7\u03c8\7\20\2\2\u03c8\u03c9\bT\1\2\u03c9"+
		"\u03ce\3\2\2\2\u03ca\u03cb\5\u00a8U\2\u03cb\u03cc\bT\1\2\u03cc\u03ce\3"+
		"\2\2\2\u03cd\u03b4\3\2\2\2\u03cd\u03b9\3\2\2\2\u03cd\u03bf\3\2\2\2\u03cd"+
		"\u03c5\3\2\2\2\u03cd\u03ca\3\2\2\2\u03ce\u00a7\3\2\2\2\u03cf\u03d0\7 "+
		"\2\2\u03d0\u03dd\bU\1\2\u03d1\u03d2\7!\2\2\u03d2\u03dd\bU\1\2\u03d3\u03d4"+
		"\7\"\2\2\u03d4\u03dd\bU\1\2\u03d5\u03d6\7B\2\2\u03d6\u03dd\bU\1\2\u03d7"+
		"\u03d8\7\5\2\2\u03d8\u03d9\5\u00a2R\2\u03d9\u03da\7\6\2\2\u03da\u03db"+
		"\bU\1\2\u03db\u03dd\3\2\2\2\u03dc\u03cf\3\2\2\2\u03dc\u03d1\3\2\2\2\u03dc"+
		"\u03d3\3\2\2\2\u03dc\u03d5\3\2\2\2\u03dc\u03d7\3\2\2\2\u03dd\u00a9\3\2"+
		"\2\2\u03de\u03e8\bV\1\2\u03df\u03e0\5\u00a2R\2\u03e0\u03e1\bV\1\2\u03e1"+
		"\u03e8\3\2\2\2\u03e2\u03e3\5\u00a2R\2\u03e3\u03e4\7\3\2\2\u03e4\u03e5"+
		"\5\u00aaV\2\u03e5\u03e6\bV\1\2\u03e6\u03e8\3\2\2\2\u03e7\u03de\3\2\2\2"+
		"\u03e7\u03df\3\2\2\2\u03e7\u03e2\3\2\2\2\u03e8\u00ab\3\2\2\2\u03e9\u03ea"+
		"\7B\2\2\u03ea\u03eb\5\u0084C\2\u03eb\u03ec\bW\1\2\u03ec\u00ad\3\2\2\2"+
		"\u03ed\u03f7\bX\1\2\u03ee\u03ef\5\u00acW\2\u03ef\u03f0\bX\1\2\u03f0\u03f7"+
		"\3\2\2\2\u03f1\u03f2\5\u00acW\2\u03f2\u03f3\7\3\2\2\u03f3\u03f4\5\u00ae"+
		"X\2\u03f4\u03f5\bX\1\2\u03f5\u03f7\3\2\2\2\u03f6\u03ed\3\2\2\2\u03f6\u03ee"+
		"\3\2\2\2\u03f6\u03f1\3\2\2\2\u03f7\u00af\3\2\2\2\u03f8\u03f9\7B\2\2\u03f9"+
		"\u03fa\7\n\2\2\u03fa\u03fb\5\u00a2R\2\u03fb\u03fc\bY\1\2\u03fc\u00b1\3"+
		"\2\2\2\u03fd\u0407\bZ\1\2\u03fe\u03ff\5\u00b0Y\2\u03ff\u0400\bZ\1\2\u0400"+
		"\u0407\3\2\2\2\u0401\u0402\5\u00b0Y\2\u0402\u0403\7\3\2\2\u0403\u0404"+
		"\5\u00b2Z\2\u0404\u0405\bZ\1\2\u0405\u0407\3\2\2\2\u0406\u03fd\3\2\2\2"+
		"\u0406\u03fe\3\2\2\2\u0406\u0401\3\2\2\2\u0407\u00b3\3\2\2\2\u0408\u0409"+
		"\5|?\2\u0409\u040a\7\n\2\2\u040a\u040b\5\u00a2R\2\u040b\u040c\b[\1\2\u040c"+
		"\u00b5\3\2\2\2(\u0172\u018b\u0197\u01b0\u01bb\u01cb\u01da\u01eb\u01f2"+
		"\u01f9\u020e\u0219\u0229\u0230\u0237\u023e\u0271\u027c\u028c\u029c\u02bf"+
		"\u02ed\u02fe\u0300\u0311\u0313\u0322\u0378\u0388\u0392\u0394\u03a8\u03b2"+
		"\u03cd\u03dc\u03e7\u03f6\u0406";
	public static final ATN _ATN =
		new ATNDeserializer().deserialize(_serializedATN.toCharArray());
	static {
		_decisionToDFA = new DFA[_ATN.getNumberOfDecisions()];
		for (int i = 0; i < _ATN.getNumberOfDecisions(); i++) {
			_decisionToDFA[i] = new DFA(_ATN.getDecisionState(i), i);
		}
	}
}