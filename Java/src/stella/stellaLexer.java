// Generated from stella/stellaLexer.g4 by ANTLR 4.9.3
package stella;
import org.antlr.v4.runtime.Lexer;
import org.antlr.v4.runtime.CharStream;
import org.antlr.v4.runtime.Token;
import org.antlr.v4.runtime.TokenStream;
import org.antlr.v4.runtime.*;
import org.antlr.v4.runtime.atn.*;
import org.antlr.v4.runtime.dfa.DFA;
import org.antlr.v4.runtime.misc.*;

@SuppressWarnings({"all", "warnings", "unchecked", "unused", "cast"})
public class stellaLexer extends Lexer {
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
	public static String[] channelNames = {
		"DEFAULT_TOKEN_CHANNEL", "HIDDEN"
	};

	public static String[] modeNames = {
		"DEFAULT_MODE"
	};

	private static String[] makeRuleNames() {
		return new String[] {
			"LETTER", "CAPITAL", "SMALL", "DIGIT", "Surrogate_id_SYMB_0", "Surrogate_id_SYMB_1", 
			"Surrogate_id_SYMB_2", "Surrogate_id_SYMB_3", "Surrogate_id_SYMB_4", 
			"Surrogate_id_SYMB_5", "Surrogate_id_SYMB_6", "Surrogate_id_SYMB_7", 
			"Surrogate_id_SYMB_8", "Surrogate_id_SYMB_9", "Surrogate_id_SYMB_10", 
			"Surrogate_id_SYMB_11", "Surrogate_id_SYMB_12", "Surrogate_id_SYMB_13", 
			"Surrogate_id_SYMB_14", "Surrogate_id_SYMB_15", "Surrogate_id_SYMB_16", 
			"Surrogate_id_SYMB_17", "Surrogate_id_SYMB_18", "Surrogate_id_SYMB_19", 
			"Surrogate_id_SYMB_20", "Surrogate_id_SYMB_21", "Surrogate_id_SYMB_22", 
			"Surrogate_id_SYMB_23", "Surrogate_id_SYMB_24", "Surrogate_id_SYMB_25", 
			"Surrogate_id_SYMB_26", "Surrogate_id_SYMB_27", "Surrogate_id_SYMB_28", 
			"Surrogate_id_SYMB_29", "Surrogate_id_SYMB_30", "Surrogate_id_SYMB_31", 
			"Surrogate_id_SYMB_32", "Surrogate_id_SYMB_33", "Surrogate_id_SYMB_34", 
			"Surrogate_id_SYMB_35", "Surrogate_id_SYMB_36", "Surrogate_id_SYMB_37", 
			"Surrogate_id_SYMB_38", "Surrogate_id_SYMB_39", "Surrogate_id_SYMB_40", 
			"Surrogate_id_SYMB_41", "Surrogate_id_SYMB_42", "Surrogate_id_SYMB_43", 
			"Surrogate_id_SYMB_44", "Surrogate_id_SYMB_45", "Surrogate_id_SYMB_46", 
			"Surrogate_id_SYMB_47", "Surrogate_id_SYMB_48", "Surrogate_id_SYMB_49", 
			"Surrogate_id_SYMB_50", "Surrogate_id_SYMB_51", "Surrogate_id_SYMB_52", 
			"Surrogate_id_SYMB_53", "Surrogate_id_SYMB_54", "Surrogate_id_SYMB_55", 
			"Surrogate_id_SYMB_56", "Surrogate_id_SYMB_57", "Surrogate_id_SYMB_58", 
			"Surrogate_id_SYMB_59", "Surrogate_id_SYMB_60", "COMMENT_antlr_builtin", 
			"MULTICOMMENT_antlr_builtin", "StellaIdent", "ExtensionName", "INTEGER", 
			"WS", "Escapable", "ErrorToken"
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


	public stellaLexer(CharStream input) {
		super(input);
		_interp = new LexerATNSimulator(this,_ATN,_decisionToDFA,_sharedContextCache);
	}

	@Override
	public String getGrammarFileName() { return "stellaLexer.g4"; }

	@Override
	public String[] getRuleNames() { return ruleNames; }

	@Override
	public String getSerializedATN() { return _serializedATN; }

	@Override
	public String[] getChannelNames() { return channelNames; }

	@Override
	public String[] getModeNames() { return modeNames; }

	@Override
	public ATN getATN() { return _ATN; }

	public static final String _serializedATN =
		"\3\u608b\ua72a\u8133\ub9ed\u417c\u3be7\u7786\u5964\2F\u01f9\b\1\4\2\t"+
		"\2\4\3\t\3\4\4\t\4\4\5\t\5\4\6\t\6\4\7\t\7\4\b\t\b\4\t\t\t\4\n\t\n\4\13"+
		"\t\13\4\f\t\f\4\r\t\r\4\16\t\16\4\17\t\17\4\20\t\20\4\21\t\21\4\22\t\22"+
		"\4\23\t\23\4\24\t\24\4\25\t\25\4\26\t\26\4\27\t\27\4\30\t\30\4\31\t\31"+
		"\4\32\t\32\4\33\t\33\4\34\t\34\4\35\t\35\4\36\t\36\4\37\t\37\4 \t \4!"+
		"\t!\4\"\t\"\4#\t#\4$\t$\4%\t%\4&\t&\4\'\t\'\4(\t(\4)\t)\4*\t*\4+\t+\4"+
		",\t,\4-\t-\4.\t.\4/\t/\4\60\t\60\4\61\t\61\4\62\t\62\4\63\t\63\4\64\t"+
		"\64\4\65\t\65\4\66\t\66\4\67\t\67\48\t8\49\t9\4:\t:\4;\t;\4<\t<\4=\t="+
		"\4>\t>\4?\t?\4@\t@\4A\tA\4B\tB\4C\tC\4D\tD\4E\tE\4F\tF\4G\tG\4H\tH\4I"+
		"\tI\4J\tJ\3\2\3\2\5\2\u0098\n\2\3\3\3\3\3\4\3\4\3\5\3\5\3\6\3\6\3\7\3"+
		"\7\3\b\3\b\3\t\3\t\3\n\3\n\3\13\3\13\3\f\3\f\3\r\3\r\3\16\3\16\3\16\3"+
		"\17\3\17\3\17\3\20\3\20\3\20\3\21\3\21\3\21\3\22\3\22\3\23\3\23\3\24\3"+
		"\24\3\25\3\25\3\25\3\26\3\26\3\27\3\27\3\27\3\30\3\30\3\30\3\31\3\31\3"+
		"\31\3\32\3\32\3\33\3\33\3\34\3\34\3\34\3\34\3\34\3\34\3\34\3\34\3\34\3"+
		"\34\3\34\3\35\3\35\3\35\3\35\3\35\3\35\3\35\3\35\3\35\3\35\3\35\3\35\3"+
		"\35\3\35\3\36\3\36\3\36\3\36\3\36\3\36\3\36\3\36\3\36\3\36\3\36\3\37\3"+
		"\37\3\37\3\37\3\37\3\37\3\37\3\37\3\37\3\37\3 \3 \3 \3 \3 \3 \3 \3 \3"+
		" \3 \3 \3 \3!\3!\3!\3!\3!\3!\3!\3!\3!\3\"\3\"\3#\3#\3#\3#\3#\3$\3$\3$"+
		"\3$\3%\3%\3%\3%\3%\3&\3&\3&\3&\3\'\3\'\3\'\3(\3(\3(\3(\3(\3)\3)\3)\3)"+
		"\3)\3*\3*\3*\3*\3*\3+\3+\3+\3+\3+\3+\3+\3,\3,\3,\3,\3,\3,\3-\3-\3-\3-"+
		"\3.\3.\3.\3/\3/\3/\3/\3/\3\60\3\60\3\60\3\61\3\61\3\61\3\62\3\62\3\62"+
		"\3\62\3\62\3\62\3\62\3\63\3\63\3\63\3\63\3\63\3\63\3\63\3\63\3\63\3\64"+
		"\3\64\3\64\3\64\3\65\3\65\3\65\3\65\3\65\3\65\3\66\3\66\3\66\3\66\3\67"+
		"\3\67\3\67\38\38\38\38\38\38\38\39\39\39\39\39\39\39\3:\3:\3:\3:\3:\3"+
		";\3;\3;\3;\3;\3<\3<\3<\3<\3<\3<\3<\3=\3=\3=\3=\3=\3>\3>\3>\3>\3>\3?\3"+
		"?\3?\3?\3?\3?\3?\3@\3@\3@\3@\3@\3@\3@\3@\3A\3A\3A\3A\3A\3B\3B\3C\3C\3"+
		"C\3C\7C\u01c0\nC\fC\16C\u01c3\13C\3C\5C\u01c6\nC\3C\3C\5C\u01ca\nC\3C"+
		"\3C\3D\3D\3D\3D\3E\3E\5E\u01d4\nE\3E\3E\3E\5E\u01d9\nE\7E\u01db\nE\fE"+
		"\16E\u01de\13E\3F\3F\3F\3F\5F\u01e4\nF\6F\u01e6\nF\rF\16F\u01e7\3G\6G"+
		"\u01eb\nG\rG\16G\u01ec\3H\6H\u01f0\nH\rH\16H\u01f1\3H\3H\3I\3I\3J\3J\2"+
		"\2K\3\2\5\2\7\2\t\2\13\3\r\4\17\5\21\6\23\7\25\b\27\t\31\n\33\13\35\f"+
		"\37\r!\16#\17%\20\'\21)\22+\23-\24/\25\61\26\63\27\65\30\67\319\32;\33"+
		"=\34?\35A\36C\37E G!I\"K#M$O%Q&S\'U(W)Y*[+],_-a.c/e\60g\61i\62k\63m\64"+
		"o\65q\66s\67u8w9y:{;}<\177=\u0081>\u0083?\u0085@\u0087A\u0089B\u008bC"+
		"\u008dD\u008fE\u0091\2\u0093F\3\2\n\5\2C\\\u00c2\u00d8\u00da\u00e0\5\2"+
		"c|\u00e1\u00f8\u00fa\u0101\3\2\62;\4\2\f\f\17\17\7\2##//<<AAaa\4\2//a"+
		"a\5\2\13\f\16\17\"\"\b\2$$^^hhppttvv\2\u0200\2\13\3\2\2\2\2\r\3\2\2\2"+
		"\2\17\3\2\2\2\2\21\3\2\2\2\2\23\3\2\2\2\2\25\3\2\2\2\2\27\3\2\2\2\2\31"+
		"\3\2\2\2\2\33\3\2\2\2\2\35\3\2\2\2\2\37\3\2\2\2\2!\3\2\2\2\2#\3\2\2\2"+
		"\2%\3\2\2\2\2\'\3\2\2\2\2)\3\2\2\2\2+\3\2\2\2\2-\3\2\2\2\2/\3\2\2\2\2"+
		"\61\3\2\2\2\2\63\3\2\2\2\2\65\3\2\2\2\2\67\3\2\2\2\29\3\2\2\2\2;\3\2\2"+
		"\2\2=\3\2\2\2\2?\3\2\2\2\2A\3\2\2\2\2C\3\2\2\2\2E\3\2\2\2\2G\3\2\2\2\2"+
		"I\3\2\2\2\2K\3\2\2\2\2M\3\2\2\2\2O\3\2\2\2\2Q\3\2\2\2\2S\3\2\2\2\2U\3"+
		"\2\2\2\2W\3\2\2\2\2Y\3\2\2\2\2[\3\2\2\2\2]\3\2\2\2\2_\3\2\2\2\2a\3\2\2"+
		"\2\2c\3\2\2\2\2e\3\2\2\2\2g\3\2\2\2\2i\3\2\2\2\2k\3\2\2\2\2m\3\2\2\2\2"+
		"o\3\2\2\2\2q\3\2\2\2\2s\3\2\2\2\2u\3\2\2\2\2w\3\2\2\2\2y\3\2\2\2\2{\3"+
		"\2\2\2\2}\3\2\2\2\2\177\3\2\2\2\2\u0081\3\2\2\2\2\u0083\3\2\2\2\2\u0085"+
		"\3\2\2\2\2\u0087\3\2\2\2\2\u0089\3\2\2\2\2\u008b\3\2\2\2\2\u008d\3\2\2"+
		"\2\2\u008f\3\2\2\2\2\u0093\3\2\2\2\3\u0097\3\2\2\2\5\u0099\3\2\2\2\7\u009b"+
		"\3\2\2\2\t\u009d\3\2\2\2\13\u009f\3\2\2\2\r\u00a1\3\2\2\2\17\u00a3\3\2"+
		"\2\2\21\u00a5\3\2\2\2\23\u00a7\3\2\2\2\25\u00a9\3\2\2\2\27\u00ab\3\2\2"+
		"\2\31\u00ad\3\2\2\2\33\u00af\3\2\2\2\35\u00b2\3\2\2\2\37\u00b5\3\2\2\2"+
		"!\u00b8\3\2\2\2#\u00bb\3\2\2\2%\u00bd\3\2\2\2\'\u00bf\3\2\2\2)\u00c1\3"+
		"\2\2\2+\u00c4\3\2\2\2-\u00c6\3\2\2\2/\u00c9\3\2\2\2\61\u00cc\3\2\2\2\63"+
		"\u00cf\3\2\2\2\65\u00d1\3\2\2\2\67\u00d3\3\2\2\29\u00de\3\2\2\2;\u00ec"+
		"\3\2\2\2=\u00f7\3\2\2\2?\u0101\3\2\2\2A\u010d\3\2\2\2C\u0116\3\2\2\2E"+
		"\u0118\3\2\2\2G\u011d\3\2\2\2I\u0121\3\2\2\2K\u0126\3\2\2\2M\u012a\3\2"+
		"\2\2O\u012d\3\2\2\2Q\u0132\3\2\2\2S\u0137\3\2\2\2U\u013c\3\2\2\2W\u0143"+
		"\3\2\2\2Y\u0149\3\2\2\2[\u014d\3\2\2\2]\u0150\3\2\2\2_\u0155\3\2\2\2a"+
		"\u0158\3\2\2\2c\u015b\3\2\2\2e\u0162\3\2\2\2g\u016b\3\2\2\2i\u016f\3\2"+
		"\2\2k\u0175\3\2\2\2m\u0179\3\2\2\2o\u017c\3\2\2\2q\u0183\3\2\2\2s\u018a"+
		"\3\2\2\2u\u018f\3\2\2\2w\u0194\3\2\2\2y\u019b\3\2\2\2{\u01a0\3\2\2\2}"+
		"\u01a5\3\2\2\2\177\u01ac\3\2\2\2\u0081\u01b4\3\2\2\2\u0083\u01b9\3\2\2"+
		"\2\u0085\u01bb\3\2\2\2\u0087\u01cd\3\2\2\2\u0089\u01d3\3\2\2\2\u008b\u01df"+
		"\3\2\2\2\u008d\u01ea\3\2\2\2\u008f\u01ef\3\2\2\2\u0091\u01f5\3\2\2\2\u0093"+
		"\u01f7\3\2\2\2\u0095\u0098\5\5\3\2\u0096\u0098\5\7\4\2\u0097\u0095\3\2"+
		"\2\2\u0097\u0096\3\2\2\2\u0098\4\3\2\2\2\u0099\u009a\t\2\2\2\u009a\6\3"+
		"\2\2\2\u009b\u009c\t\3\2\2\u009c\b\3\2\2\2\u009d\u009e\t\4\2\2\u009e\n"+
		"\3\2\2\2\u009f\u00a0\7.\2\2\u00a0\f\3\2\2\2\u00a1\u00a2\7=\2\2\u00a2\16"+
		"\3\2\2\2\u00a3\u00a4\7*\2\2\u00a4\20\3\2\2\2\u00a5\u00a6\7+\2\2\u00a6"+
		"\22\3\2\2\2\u00a7\u00a8\7}\2\2\u00a8\24\3\2\2\2\u00a9\u00aa\7\177\2\2"+
		"\u00aa\26\3\2\2\2\u00ab\u00ac\7?\2\2\u00ac\30\3\2\2\2\u00ad\u00ae\7<\2"+
		"\2\u00ae\32\3\2\2\2\u00af\u00b0\7/\2\2\u00b0\u00b1\7@\2\2\u00b1\34\3\2"+
		"\2\2\u00b2\u00b3\7?\2\2\u00b3\u00b4\7@\2\2\u00b4\36\3\2\2\2\u00b5\u00b6"+
		"\7>\2\2\u00b6\u00b7\7~\2\2\u00b7 \3\2\2\2\u00b8\u00b9\7~\2\2\u00b9\u00ba"+
		"\7@\2\2\u00ba\"\3\2\2\2\u00bb\u00bc\7]\2\2\u00bc$\3\2\2\2\u00bd\u00be"+
		"\7_\2\2\u00be&\3\2\2\2\u00bf\u00c0\7>\2\2\u00c0(\3\2\2\2\u00c1\u00c2\7"+
		">\2\2\u00c2\u00c3\7?\2\2\u00c3*\3\2\2\2\u00c4\u00c5\7@\2\2\u00c5,\3\2"+
		"\2\2\u00c6\u00c7\7@\2\2\u00c7\u00c8\7?\2\2\u00c8.\3\2\2\2\u00c9\u00ca"+
		"\7?\2\2\u00ca\u00cb\7?\2\2\u00cb\60\3\2\2\2\u00cc\u00cd\7#\2\2\u00cd\u00ce"+
		"\7?\2\2\u00ce\62\3\2\2\2\u00cf\u00d0\7-\2\2\u00d0\64\3\2\2\2\u00d1\u00d2"+
		"\7,\2\2\u00d2\66\3\2\2\2\u00d3\u00d4\7N\2\2\u00d4\u00d5\7k\2\2\u00d5\u00d6"+
		"\7u\2\2\u00d6\u00d7\7v\2\2\u00d7\u00d8\7<\2\2\u00d8\u00d9\7<\2\2\u00d9"+
		"\u00da\7j\2\2\u00da\u00db\7g\2\2\u00db\u00dc\7c\2\2\u00dc\u00dd\7f\2\2"+
		"\u00dd8\3\2\2\2\u00de\u00df\7N\2\2\u00df\u00e0\7k\2\2\u00e0\u00e1\7u\2"+
		"\2\u00e1\u00e2\7v\2\2\u00e2\u00e3\7<\2\2\u00e3\u00e4\7<\2\2\u00e4\u00e5"+
		"\7k\2\2\u00e5\u00e6\7u\2\2\u00e6\u00e7\7g\2\2\u00e7\u00e8\7o\2\2\u00e8"+
		"\u00e9\7r\2\2\u00e9\u00ea\7v\2\2\u00ea\u00eb\7{\2\2\u00eb:\3\2\2\2\u00ec"+
		"\u00ed\7N\2\2\u00ed\u00ee\7k\2\2\u00ee\u00ef\7u\2\2\u00ef\u00f0\7v\2\2"+
		"\u00f0\u00f1\7<\2\2\u00f1\u00f2\7<\2\2\u00f2\u00f3\7v\2\2\u00f3\u00f4"+
		"\7c\2\2\u00f4\u00f5\7k\2\2\u00f5\u00f6\7n\2\2\u00f6<\3\2\2\2\u00f7\u00f8"+
		"\7P\2\2\u00f8\u00f9\7c\2\2\u00f9\u00fa\7v\2\2\u00fa\u00fb\7<\2\2\u00fb"+
		"\u00fc\7<\2\2\u00fc\u00fd\7r\2\2\u00fd\u00fe\7t\2\2\u00fe\u00ff\7g\2\2"+
		"\u00ff\u0100\7f\2\2\u0100>\3\2\2\2\u0101\u0102\7P\2\2\u0102\u0103\7c\2"+
		"\2\u0103\u0104\7v\2\2\u0104\u0105\7<\2\2\u0105\u0106\7<\2\2\u0106\u0107"+
		"\7k\2\2\u0107\u0108\7u\2\2\u0108\u0109\7|\2\2\u0109\u010a\7g\2\2\u010a"+
		"\u010b\7t\2\2\u010b\u010c\7q\2\2\u010c@\3\2\2\2\u010d\u010e\7P\2\2\u010e"+
		"\u010f\7c\2\2\u010f\u0110\7v\2\2\u0110\u0111\7<\2\2\u0111\u0112\7<\2\2"+
		"\u0112\u0113\7t\2\2\u0113\u0114\7g\2\2\u0114\u0115\7e\2\2\u0115B\3\2\2"+
		"\2\u0116\u0117\7\60\2\2\u0117D\3\2\2\2\u0118\u0119\7D\2\2\u0119\u011a"+
		"\7q\2\2\u011a\u011b\7q\2\2\u011b\u011c\7n\2\2\u011cF\3\2\2\2\u011d\u011e"+
		"\7P\2\2\u011e\u011f\7c\2\2\u011f\u0120\7v\2\2\u0120H\3\2\2\2\u0121\u0122"+
		"\7W\2\2\u0122\u0123\7p\2\2\u0123\u0124\7k\2\2\u0124\u0125\7v\2\2\u0125"+
		"J\3\2\2\2\u0126\u0127\7c\2\2\u0127\u0128\7p\2\2\u0128\u0129\7f\2\2\u0129"+
		"L\3\2\2\2\u012a\u012b\7c\2\2\u012b\u012c\7u\2\2\u012cN\3\2\2\2\u012d\u012e"+
		"\7e\2\2\u012e\u012f\7q\2\2\u012f\u0130\7p\2\2\u0130\u0131\7u\2\2\u0131"+
		"P\3\2\2\2\u0132\u0133\7e\2\2\u0133\u0134\7q\2\2\u0134\u0135\7t\2\2\u0135"+
		"\u0136\7g\2\2\u0136R\3\2\2\2\u0137\u0138\7g\2\2\u0138\u0139\7n\2\2\u0139"+
		"\u013a\7u\2\2\u013a\u013b\7g\2\2\u013bT\3\2\2\2\u013c\u013d\7g\2\2\u013d"+
		"\u013e\7z\2\2\u013e\u013f\7v\2\2\u013f\u0140\7g\2\2\u0140\u0141\7p\2\2"+
		"\u0141\u0142\7f\2\2\u0142V\3\2\2\2\u0143\u0144\7h\2\2\u0144\u0145\7c\2"+
		"\2\u0145\u0146\7n\2\2\u0146\u0147\7u\2\2\u0147\u0148\7g\2\2\u0148X\3\2"+
		"\2\2\u0149\u014a\7h\2\2\u014a\u014b\7k\2\2\u014b\u014c\7z\2\2\u014cZ\3"+
		"\2\2\2\u014d\u014e\7h\2\2\u014e\u014f\7p\2\2\u014f\\\3\2\2\2\u0150\u0151"+
		"\7h\2\2\u0151\u0152\7q\2\2\u0152\u0153\7n\2\2\u0153\u0154\7f\2\2\u0154"+
		"^\3\2\2\2\u0155\u0156\7k\2\2\u0156\u0157\7h\2\2\u0157`\3\2\2\2\u0158\u0159"+
		"\7k\2\2\u0159\u015a\7p\2\2\u015ab\3\2\2\2\u015b\u015c\7k\2\2\u015c\u015d"+
		"\7p\2\2\u015d\u015e\7n\2\2\u015e\u015f\7k\2\2\u015f\u0160\7p\2\2\u0160"+
		"\u0161\7g\2\2\u0161d\3\2\2\2\u0162\u0163\7n\2\2\u0163\u0164\7c\2\2\u0164"+
		"\u0165\7p\2\2\u0165\u0166\7i\2\2\u0166\u0167\7w\2\2\u0167\u0168\7c\2\2"+
		"\u0168\u0169\7i\2\2\u0169\u016a\7g\2\2\u016af\3\2\2\2\u016b\u016c\7n\2"+
		"\2\u016c\u016d\7g\2\2\u016d\u016e\7v\2\2\u016eh\3\2\2\2\u016f\u0170\7"+
		"o\2\2\u0170\u0171\7c\2\2\u0171\u0172\7v\2\2\u0172\u0173\7e\2\2\u0173\u0174"+
		"\7j\2\2\u0174j\3\2\2\2\u0175\u0176\7p\2\2\u0176\u0177\7q\2\2\u0177\u0178"+
		"\7v\2\2\u0178l\3\2\2\2\u0179\u017a\7q\2\2\u017a\u017b\7t\2\2\u017bn\3"+
		"\2\2\2\u017c\u017d\7t\2\2\u017d\u017e\7g\2\2\u017e\u017f\7e\2\2\u017f"+
		"\u0180\7q\2\2\u0180\u0181\7t\2\2\u0181\u0182\7f\2\2\u0182p\3\2\2\2\u0183"+
		"\u0184\7t\2\2\u0184\u0185\7g\2\2\u0185\u0186\7v\2\2\u0186\u0187\7w\2\2"+
		"\u0187\u0188\7t\2\2\u0188\u0189\7p\2\2\u0189r\3\2\2\2\u018a\u018b\7u\2"+
		"\2\u018b\u018c\7w\2\2\u018c\u018d\7e\2\2\u018d\u018e\7e\2\2\u018et\3\2"+
		"\2\2\u018f\u0190\7v\2\2\u0190\u0191\7j\2\2\u0191\u0192\7g\2\2\u0192\u0193"+
		"\7p\2\2\u0193v\3\2\2\2\u0194\u0195\7v\2\2\u0195\u0196\7j\2\2\u0196\u0197"+
		"\7t\2\2\u0197\u0198\7q\2\2\u0198\u0199\7y\2\2\u0199\u019a\7u\2\2\u019a"+
		"x\3\2\2\2\u019b\u019c\7v\2\2\u019c\u019d\7t\2\2\u019d\u019e\7w\2\2\u019e"+
		"\u019f\7g\2\2\u019fz\3\2\2\2\u01a0\u01a1\7v\2\2\u01a1\u01a2\7{\2\2\u01a2"+
		"\u01a3\7r\2\2\u01a3\u01a4\7g\2\2\u01a4|\3\2\2\2\u01a5\u01a6\7w\2\2\u01a6"+
		"\u01a7\7p\2\2\u01a7\u01a8\7h\2\2\u01a8\u01a9\7q\2\2\u01a9\u01aa\7n\2\2"+
		"\u01aa\u01ab\7f\2\2\u01ab~\3\2\2\2\u01ac\u01ad\7x\2\2\u01ad\u01ae\7c\2"+
		"\2\u01ae\u01af\7t\2\2\u01af\u01b0\7k\2\2\u01b0\u01b1\7c\2\2\u01b1\u01b2"+
		"\7p\2\2\u01b2\u01b3\7v\2\2\u01b3\u0080\3\2\2\2\u01b4\u01b5\7y\2\2\u01b5"+
		"\u01b6\7k\2\2\u01b6\u01b7\7v\2\2\u01b7\u01b8\7j\2\2\u01b8\u0082\3\2\2"+
		"\2\u01b9\u01ba\7\u00b7\2\2\u01ba\u0084\3\2\2\2\u01bb\u01bc\7\61\2\2\u01bc"+
		"\u01bd\7\61\2\2\u01bd\u01c1\3\2\2\2\u01be\u01c0\n\5\2\2\u01bf\u01be\3"+
		"\2\2\2\u01c0\u01c3\3\2\2\2\u01c1\u01bf\3\2\2\2\u01c1\u01c2\3\2\2\2\u01c2"+
		"\u01c9\3\2\2\2\u01c3\u01c1\3\2\2\2\u01c4\u01c6\7\17\2\2\u01c5\u01c4\3"+
		"\2\2\2\u01c5\u01c6\3\2\2\2\u01c6\u01c7\3\2\2\2\u01c7\u01ca\7\f\2\2\u01c8"+
		"\u01ca\7\2\2\3\u01c9\u01c5\3\2\2\2\u01c9\u01c8\3\2\2\2\u01ca\u01cb\3\2"+
		"\2\2\u01cb\u01cc\bC\2\2\u01cc\u0086\3\2\2\2\u01cd\u01ce\3\2\2\2\u01ce"+
		"\u01cf\3\2\2\2\u01cf\u01d0\bD\2\2\u01d0\u0088\3\2\2\2\u01d1\u01d4\7a\2"+
		"\2\u01d2\u01d4\5\3\2\2\u01d3\u01d1\3\2\2\2\u01d3\u01d2\3\2\2\2\u01d4\u01dc"+
		"\3\2\2\2\u01d5\u01db\t\6\2\2\u01d6\u01d9\5\t\5\2\u01d7\u01d9\5\3\2\2\u01d8"+
		"\u01d6\3\2\2\2\u01d8\u01d7\3\2\2\2\u01d9\u01db\3\2\2\2\u01da\u01d5\3\2"+
		"\2\2\u01da\u01d8\3\2\2\2\u01db\u01de\3\2\2\2\u01dc\u01da\3\2\2\2\u01dc"+
		"\u01dd\3\2\2\2\u01dd\u008a\3\2\2\2\u01de\u01dc\3\2\2\2\u01df\u01e5\7%"+
		"\2\2\u01e0\u01e6\t\7\2\2\u01e1\u01e4\5\t\5\2\u01e2\u01e4\5\3\2\2\u01e3"+
		"\u01e1\3\2\2\2\u01e3\u01e2\3\2\2\2\u01e4\u01e6\3\2\2\2\u01e5\u01e0\3\2"+
		"\2\2\u01e5\u01e3\3\2\2\2\u01e6\u01e7\3\2\2\2\u01e7\u01e5\3\2\2\2\u01e7"+
		"\u01e8\3\2\2\2\u01e8\u008c\3\2\2\2\u01e9\u01eb\5\t\5\2\u01ea\u01e9\3\2"+
		"\2\2\u01eb\u01ec\3\2\2\2\u01ec\u01ea\3\2\2\2\u01ec\u01ed\3\2\2\2\u01ed"+
		"\u008e\3\2\2\2\u01ee\u01f0\t\b\2\2\u01ef\u01ee\3\2\2\2\u01f0\u01f1\3\2"+
		"\2\2\u01f1\u01ef\3\2\2\2\u01f1\u01f2\3\2\2\2\u01f2\u01f3\3\2\2\2\u01f3"+
		"\u01f4\bH\2\2\u01f4\u0090\3\2\2\2\u01f5\u01f6\t\t\2\2\u01f6\u0092\3\2"+
		"\2\2\u01f7\u01f8\13\2\2\2\u01f8\u0094\3\2\2\2\20\2\u0097\u01c1\u01c5\u01c9"+
		"\u01d3\u01d8\u01da\u01dc\u01e3\u01e5\u01e7\u01ec\u01f1\3\b\2\2";
	public static final ATN _ATN =
		new ATNDeserializer().deserialize(_serializedATN.toCharArray());
	static {
		_decisionToDFA = new DFA[_ATN.getNumberOfDecisions()];
		for (int i = 0; i < _ATN.getNumberOfDecisions(); i++) {
			_decisionToDFA[i] = new DFA(_ATN.getDecisionState(i), i);
		}
	}
}