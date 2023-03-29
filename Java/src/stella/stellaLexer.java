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
		Surrogate_id_SYMB_59=60, COMMENT_antlr_builtin=61, MULTICOMMENT_antlr_builtin=62, 
		StellaIdent=63, ExtensionName=64, INTEGER=65, WS=66, ErrorToken=67;
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
			"Surrogate_id_SYMB_59", "COMMENT_antlr_builtin", "MULTICOMMENT_antlr_builtin", 
			"StellaIdent", "ExtensionName", "INTEGER", "WS", "Escapable", "ErrorToken"
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
		"\3\u608b\ua72a\u8133\ub9ed\u417c\u3be7\u7786\u5964\2E\u01fb\b\1\4\2\t"+
		"\2\4\3\t\3\4\4\t\4\4\5\t\5\4\6\t\6\4\7\t\7\4\b\t\b\4\t\t\t\4\n\t\n\4\13"+
		"\t\13\4\f\t\f\4\r\t\r\4\16\t\16\4\17\t\17\4\20\t\20\4\21\t\21\4\22\t\22"+
		"\4\23\t\23\4\24\t\24\4\25\t\25\4\26\t\26\4\27\t\27\4\30\t\30\4\31\t\31"+
		"\4\32\t\32\4\33\t\33\4\34\t\34\4\35\t\35\4\36\t\36\4\37\t\37\4 \t \4!"+
		"\t!\4\"\t\"\4#\t#\4$\t$\4%\t%\4&\t&\4\'\t\'\4(\t(\4)\t)\4*\t*\4+\t+\4"+
		",\t,\4-\t-\4.\t.\4/\t/\4\60\t\60\4\61\t\61\4\62\t\62\4\63\t\63\4\64\t"+
		"\64\4\65\t\65\4\66\t\66\4\67\t\67\48\t8\49\t9\4:\t:\4;\t;\4<\t<\4=\t="+
		"\4>\t>\4?\t?\4@\t@\4A\tA\4B\tB\4C\tC\4D\tD\4E\tE\4F\tF\4G\tG\4H\tH\4I"+
		"\tI\3\2\3\2\5\2\u0096\n\2\3\3\3\3\3\4\3\4\3\5\3\5\3\6\3\6\3\7\3\7\3\b"+
		"\3\b\3\t\3\t\3\n\3\n\3\13\3\13\3\f\3\f\3\r\3\r\3\16\3\16\3\16\3\17\3\17"+
		"\3\17\3\20\3\20\3\21\3\21\3\22\3\22\3\23\3\23\3\24\3\24\3\24\3\25\3\25"+
		"\3\25\3\26\3\26\3\26\3\27\3\27\3\27\3\30\3\30\3\31\3\31\3\32\3\32\3\32"+
		"\3\32\3\32\3\32\3\32\3\32\3\32\3\32\3\32\3\33\3\33\3\33\3\33\3\33\3\33"+
		"\3\33\3\33\3\33\3\33\3\33\3\33\3\33\3\33\3\34\3\34\3\34\3\34\3\34\3\34"+
		"\3\34\3\34\3\34\3\34\3\34\3\35\3\35\3\35\3\35\3\35\3\35\3\35\3\35\3\35"+
		"\3\35\3\36\3\36\3\36\3\36\3\36\3\36\3\36\3\36\3\36\3\36\3\36\3\36\3\37"+
		"\3\37\3\37\3\37\3\37\3\37\3\37\3\37\3\37\3 \3 \3!\3!\3!\3!\3!\3\"\3\""+
		"\3\"\3\"\3#\3#\3#\3#\3#\3$\3$\3$\3$\3%\3%\3%\3&\3&\3&\3&\3&\3\'\3\'\3"+
		"\'\3\'\3\'\3(\3(\3(\3(\3(\3)\3)\3)\3)\3)\3)\3)\3*\3*\3*\3*\3*\3*\3+\3"+
		"+\3+\3+\3,\3,\3,\3-\3-\3-\3-\3-\3.\3.\3.\3/\3/\3/\3\60\3\60\3\60\3\60"+
		"\3\60\3\60\3\60\3\61\3\61\3\61\3\61\3\61\3\61\3\61\3\61\3\61\3\62\3\62"+
		"\3\62\3\62\3\63\3\63\3\63\3\63\3\63\3\63\3\64\3\64\3\64\3\64\3\65\3\65"+
		"\3\65\3\66\3\66\3\66\3\66\3\66\3\66\3\66\3\67\3\67\3\67\3\67\3\67\3\67"+
		"\3\67\38\38\38\38\38\38\38\39\39\39\39\39\3:\3:\3:\3:\3:\3;\3;\3;\3;\3"+
		";\3;\3;\3<\3<\3<\3<\3<\3=\3=\3=\3=\3=\3>\3>\3>\3>\3>\3>\3>\3?\3?\3?\3"+
		"?\3?\3?\3?\3?\3@\3@\3@\3@\3@\3A\3A\3B\3B\3B\3B\7B\u01bf\nB\fB\16B\u01c2"+
		"\13B\3B\5B\u01c5\nB\3B\3B\5B\u01c9\nB\3B\3B\3C\3C\3C\3C\3D\3D\5D\u01d3"+
		"\nD\3D\3D\3D\5D\u01d8\nD\7D\u01da\nD\fD\16D\u01dd\13D\3E\3E\3E\3E\5E\u01e3"+
		"\nE\7E\u01e5\nE\fE\16E\u01e8\13E\3E\3E\3F\6F\u01ed\nF\rF\16F\u01ee\3G"+
		"\6G\u01f2\nG\rG\16G\u01f3\3G\3G\3H\3H\3I\3I\2\2J\3\2\5\2\7\2\t\2\13\3"+
		"\r\4\17\5\21\6\23\7\25\b\27\t\31\n\33\13\35\f\37\r!\16#\17%\20\'\21)\22"+
		"+\23-\24/\25\61\26\63\27\65\30\67\319\32;\33=\34?\35A\36C\37E G!I\"K#"+
		"M$O%Q&S\'U(W)Y*[+],_-a.c/e\60g\61i\62k\63m\64o\65q\66s\67u8w9y:{;}<\177"+
		"=\u0081>\u0083?\u0085@\u0087A\u0089B\u008bC\u008dD\u008f\2\u0091E\3\2"+
		"\n\5\2C\\\u00c2\u00d8\u00da\u00e0\5\2c|\u00e1\u00f8\u00fa\u0101\3\2\62"+
		";\4\2\f\f\17\17\4\2<<aa\5\2\"\"//aa\5\2\13\f\16\17\"\"\b\2$$^^hhppttv"+
		"v\2\u0202\2\13\3\2\2\2\2\r\3\2\2\2\2\17\3\2\2\2\2\21\3\2\2\2\2\23\3\2"+
		"\2\2\2\25\3\2\2\2\2\27\3\2\2\2\2\31\3\2\2\2\2\33\3\2\2\2\2\35\3\2\2\2"+
		"\2\37\3\2\2\2\2!\3\2\2\2\2#\3\2\2\2\2%\3\2\2\2\2\'\3\2\2\2\2)\3\2\2\2"+
		"\2+\3\2\2\2\2-\3\2\2\2\2/\3\2\2\2\2\61\3\2\2\2\2\63\3\2\2\2\2\65\3\2\2"+
		"\2\2\67\3\2\2\2\29\3\2\2\2\2;\3\2\2\2\2=\3\2\2\2\2?\3\2\2\2\2A\3\2\2\2"+
		"\2C\3\2\2\2\2E\3\2\2\2\2G\3\2\2\2\2I\3\2\2\2\2K\3\2\2\2\2M\3\2\2\2\2O"+
		"\3\2\2\2\2Q\3\2\2\2\2S\3\2\2\2\2U\3\2\2\2\2W\3\2\2\2\2Y\3\2\2\2\2[\3\2"+
		"\2\2\2]\3\2\2\2\2_\3\2\2\2\2a\3\2\2\2\2c\3\2\2\2\2e\3\2\2\2\2g\3\2\2\2"+
		"\2i\3\2\2\2\2k\3\2\2\2\2m\3\2\2\2\2o\3\2\2\2\2q\3\2\2\2\2s\3\2\2\2\2u"+
		"\3\2\2\2\2w\3\2\2\2\2y\3\2\2\2\2{\3\2\2\2\2}\3\2\2\2\2\177\3\2\2\2\2\u0081"+
		"\3\2\2\2\2\u0083\3\2\2\2\2\u0085\3\2\2\2\2\u0087\3\2\2\2\2\u0089\3\2\2"+
		"\2\2\u008b\3\2\2\2\2\u008d\3\2\2\2\2\u0091\3\2\2\2\3\u0095\3\2\2\2\5\u0097"+
		"\3\2\2\2\7\u0099\3\2\2\2\t\u009b\3\2\2\2\13\u009d\3\2\2\2\r\u009f\3\2"+
		"\2\2\17\u00a1\3\2\2\2\21\u00a3\3\2\2\2\23\u00a5\3\2\2\2\25\u00a7\3\2\2"+
		"\2\27\u00a9\3\2\2\2\31\u00ab\3\2\2\2\33\u00ad\3\2\2\2\35\u00b0\3\2\2\2"+
		"\37\u00b3\3\2\2\2!\u00b5\3\2\2\2#\u00b7\3\2\2\2%\u00b9\3\2\2\2\'\u00bb"+
		"\3\2\2\2)\u00be\3\2\2\2+\u00c1\3\2\2\2-\u00c4\3\2\2\2/\u00c7\3\2\2\2\61"+
		"\u00c9\3\2\2\2\63\u00cb\3\2\2\2\65\u00d6\3\2\2\2\67\u00e4\3\2\2\29\u00ef"+
		"\3\2\2\2;\u00f9\3\2\2\2=\u0105\3\2\2\2?\u010e\3\2\2\2A\u0110\3\2\2\2C"+
		"\u0115\3\2\2\2E\u0119\3\2\2\2G\u011e\3\2\2\2I\u0122\3\2\2\2K\u0125\3\2"+
		"\2\2M\u012a\3\2\2\2O\u012f\3\2\2\2Q\u0134\3\2\2\2S\u013b\3\2\2\2U\u0141"+
		"\3\2\2\2W\u0145\3\2\2\2Y\u0148\3\2\2\2[\u014d\3\2\2\2]\u0150\3\2\2\2_"+
		"\u0153\3\2\2\2a\u015a\3\2\2\2c\u0163\3\2\2\2e\u0167\3\2\2\2g\u016d\3\2"+
		"\2\2i\u0171\3\2\2\2k\u0174\3\2\2\2m\u017b\3\2\2\2o\u0182\3\2\2\2q\u0189"+
		"\3\2\2\2s\u018e\3\2\2\2u\u0193\3\2\2\2w\u019a\3\2\2\2y\u019f\3\2\2\2{"+
		"\u01a4\3\2\2\2}\u01ab\3\2\2\2\177\u01b3\3\2\2\2\u0081\u01b8\3\2\2\2\u0083"+
		"\u01ba\3\2\2\2\u0085\u01cc\3\2\2\2\u0087\u01d2\3\2\2\2\u0089\u01de\3\2"+
		"\2\2\u008b\u01ec\3\2\2\2\u008d\u01f1\3\2\2\2\u008f\u01f7\3\2\2\2\u0091"+
		"\u01f9\3\2\2\2\u0093\u0096\5\5\3\2\u0094\u0096\5\7\4\2\u0095\u0093\3\2"+
		"\2\2\u0095\u0094\3\2\2\2\u0096\4\3\2\2\2\u0097\u0098\t\2\2\2\u0098\6\3"+
		"\2\2\2\u0099\u009a\t\3\2\2\u009a\b\3\2\2\2\u009b\u009c\t\4\2\2\u009c\n"+
		"\3\2\2\2\u009d\u009e\7=\2\2\u009e\f\3\2\2\2\u009f\u00a0\7.\2\2\u00a0\16"+
		"\3\2\2\2\u00a1\u00a2\7*\2\2\u00a2\20\3\2\2\2\u00a3\u00a4\7+\2\2\u00a4"+
		"\22\3\2\2\2\u00a5\u00a6\7}\2\2\u00a6\24\3\2\2\2\u00a7\u00a8\7\177\2\2"+
		"\u00a8\26\3\2\2\2\u00a9\u00aa\7?\2\2\u00aa\30\3\2\2\2\u00ab\u00ac\7<\2"+
		"\2\u00ac\32\3\2\2\2\u00ad\u00ae\7/\2\2\u00ae\u00af\7@\2\2\u00af\34\3\2"+
		"\2\2\u00b0\u00b1\7?\2\2\u00b1\u00b2\7@\2\2\u00b2\36\3\2\2\2\u00b3\u00b4"+
		"\7>\2\2\u00b4 \3\2\2\2\u00b5\u00b6\7@\2\2\u00b6\"\3\2\2\2\u00b7\u00b8"+
		"\7]\2\2\u00b8$\3\2\2\2\u00b9\u00ba\7_\2\2\u00ba&\3\2\2\2\u00bb\u00bc\7"+
		">\2\2\u00bc\u00bd\7?\2\2\u00bd(\3\2\2\2\u00be\u00bf\7@\2\2\u00bf\u00c0"+
		"\7?\2\2\u00c0*\3\2\2\2\u00c1\u00c2\7?\2\2\u00c2\u00c3\7?\2\2\u00c3,\3"+
		"\2\2\2\u00c4\u00c5\7#\2\2\u00c5\u00c6\7?\2\2\u00c6.\3\2\2\2\u00c7\u00c8"+
		"\7-\2\2\u00c8\60\3\2\2\2\u00c9\u00ca\7,\2\2\u00ca\62\3\2\2\2\u00cb\u00cc"+
		"\7N\2\2\u00cc\u00cd\7k\2\2\u00cd\u00ce\7u\2\2\u00ce\u00cf\7v\2\2\u00cf"+
		"\u00d0\7<\2\2\u00d0\u00d1\7<\2\2\u00d1\u00d2\7j\2\2\u00d2\u00d3\7g\2\2"+
		"\u00d3\u00d4\7c\2\2\u00d4\u00d5\7f\2\2\u00d5\64\3\2\2\2\u00d6\u00d7\7"+
		"N\2\2\u00d7\u00d8\7k\2\2\u00d8\u00d9\7u\2\2\u00d9\u00da\7v\2\2\u00da\u00db"+
		"\7<\2\2\u00db\u00dc\7<\2\2\u00dc\u00dd\7k\2\2\u00dd\u00de\7u\2\2\u00de"+
		"\u00df\7g\2\2\u00df\u00e0\7o\2\2\u00e0\u00e1\7r\2\2\u00e1\u00e2\7v\2\2"+
		"\u00e2\u00e3\7{\2\2\u00e3\66\3\2\2\2\u00e4\u00e5\7N\2\2\u00e5\u00e6\7"+
		"k\2\2\u00e6\u00e7\7u\2\2\u00e7\u00e8\7v\2\2\u00e8\u00e9\7<\2\2\u00e9\u00ea"+
		"\7<\2\2\u00ea\u00eb\7v\2\2\u00eb\u00ec\7c\2\2\u00ec\u00ed\7k\2\2\u00ed"+
		"\u00ee\7n\2\2\u00ee8\3\2\2\2\u00ef\u00f0\7P\2\2\u00f0\u00f1\7c\2\2\u00f1"+
		"\u00f2\7v\2\2\u00f2\u00f3\7<\2\2\u00f3\u00f4\7<\2\2\u00f4\u00f5\7r\2\2"+
		"\u00f5\u00f6\7t\2\2\u00f6\u00f7\7g\2\2\u00f7\u00f8\7f\2\2\u00f8:\3\2\2"+
		"\2\u00f9\u00fa\7P\2\2\u00fa\u00fb\7c\2\2\u00fb\u00fc\7v\2\2\u00fc\u00fd"+
		"\7<\2\2\u00fd\u00fe\7<\2\2\u00fe\u00ff\7k\2\2\u00ff\u0100\7u\2\2\u0100"+
		"\u0101\7|\2\2\u0101\u0102\7g\2\2\u0102\u0103\7t\2\2\u0103\u0104\7q\2\2"+
		"\u0104<\3\2\2\2\u0105\u0106\7P\2\2\u0106\u0107\7c\2\2\u0107\u0108\7v\2"+
		"\2\u0108\u0109\7<\2\2\u0109\u010a\7<\2\2\u010a\u010b\7t\2\2\u010b\u010c"+
		"\7g\2\2\u010c\u010d\7e\2\2\u010d>\3\2\2\2\u010e\u010f\7\60\2\2\u010f@"+
		"\3\2\2\2\u0110\u0111\7D\2\2\u0111\u0112\7q\2\2\u0112\u0113\7q\2\2\u0113"+
		"\u0114\7n\2\2\u0114B\3\2\2\2\u0115\u0116\7P\2\2\u0116\u0117\7c\2\2\u0117"+
		"\u0118\7v\2\2\u0118D\3\2\2\2\u0119\u011a\7W\2\2\u011a\u011b\7p\2\2\u011b"+
		"\u011c\7k\2\2\u011c\u011d\7v\2\2\u011dF\3\2\2\2\u011e\u011f\7c\2\2\u011f"+
		"\u0120\7p\2\2\u0120\u0121\7f\2\2\u0121H\3\2\2\2\u0122\u0123\7c\2\2\u0123"+
		"\u0124\7u\2\2\u0124J\3\2\2\2\u0125\u0126\7e\2\2\u0126\u0127\7q\2\2\u0127"+
		"\u0128\7p\2\2\u0128\u0129\7u\2\2\u0129L\3\2\2\2\u012a\u012b\7e\2\2\u012b"+
		"\u012c\7q\2\2\u012c\u012d\7t\2\2\u012d\u012e\7g\2\2\u012eN\3\2\2\2\u012f"+
		"\u0130\7g\2\2\u0130\u0131\7n\2\2\u0131\u0132\7u\2\2\u0132\u0133\7g\2\2"+
		"\u0133P\3\2\2\2\u0134\u0135\7g\2\2\u0135\u0136\7z\2\2\u0136\u0137\7v\2"+
		"\2\u0137\u0138\7g\2\2\u0138\u0139\7p\2\2\u0139\u013a\7f\2\2\u013aR\3\2"+
		"\2\2\u013b\u013c\7h\2\2\u013c\u013d\7c\2\2\u013d\u013e\7n\2\2\u013e\u013f"+
		"\7u\2\2\u013f\u0140\7g\2\2\u0140T\3\2\2\2\u0141\u0142\7h\2\2\u0142\u0143"+
		"\7k\2\2\u0143\u0144\7z\2\2\u0144V\3\2\2\2\u0145\u0146\7h\2\2\u0146\u0147"+
		"\7p\2\2\u0147X\3\2\2\2\u0148\u0149\7h\2\2\u0149\u014a\7q\2\2\u014a\u014b"+
		"\7n\2\2\u014b\u014c\7f\2\2\u014cZ\3\2\2\2\u014d\u014e\7k\2\2\u014e\u014f"+
		"\7h\2\2\u014f\\\3\2\2\2\u0150\u0151\7k\2\2\u0151\u0152\7p\2\2\u0152^\3"+
		"\2\2\2\u0153\u0154\7k\2\2\u0154\u0155\7p\2\2\u0155\u0156\7n\2\2\u0156"+
		"\u0157\7k\2\2\u0157\u0158\7p\2\2\u0158\u0159\7g\2\2\u0159`\3\2\2\2\u015a"+
		"\u015b\7n\2\2\u015b\u015c\7c\2\2\u015c\u015d\7p\2\2\u015d\u015e\7i\2\2"+
		"\u015e\u015f\7w\2\2\u015f\u0160\7c\2\2\u0160\u0161\7i\2\2\u0161\u0162"+
		"\7g\2\2\u0162b\3\2\2\2\u0163\u0164\7n\2\2\u0164\u0165\7g\2\2\u0165\u0166"+
		"\7v\2\2\u0166d\3\2\2\2\u0167\u0168\7o\2\2\u0168\u0169\7c\2\2\u0169\u016a"+
		"\7v\2\2\u016a\u016b\7e\2\2\u016b\u016c\7j\2\2\u016cf\3\2\2\2\u016d\u016e"+
		"\7p\2\2\u016e\u016f\7q\2\2\u016f\u0170\7v\2\2\u0170h\3\2\2\2\u0171\u0172"+
		"\7q\2\2\u0172\u0173\7t\2\2\u0173j\3\2\2\2\u0174\u0175\7t\2\2\u0175\u0176"+
		"\7g\2\2\u0176\u0177\7e\2\2\u0177\u0178\7q\2\2\u0178\u0179\7t\2\2\u0179"+
		"\u017a\7f\2\2\u017al\3\2\2\2\u017b\u017c\7t\2\2\u017c\u017d\7g\2\2\u017d"+
		"\u017e\7v\2\2\u017e\u017f\7w\2\2\u017f\u0180\7t\2\2\u0180\u0181\7p\2\2"+
		"\u0181n\3\2\2\2\u0182\u0183\7u\2\2\u0183\u0184\7v\2\2\u0184\u0185\7t\2"+
		"\2\u0185\u0186\7w\2\2\u0186\u0187\7e\2\2\u0187\u0188\7v\2\2\u0188p\3\2"+
		"\2\2\u0189\u018a\7u\2\2\u018a\u018b\7w\2\2\u018b\u018c\7e\2\2\u018c\u018d"+
		"\7e\2\2\u018dr\3\2\2\2\u018e\u018f\7v\2\2\u018f\u0190\7j\2\2\u0190\u0191"+
		"\7g\2\2\u0191\u0192\7p\2\2\u0192t\3\2\2\2\u0193\u0194\7v\2\2\u0194\u0195"+
		"\7j\2\2\u0195\u0196\7t\2\2\u0196\u0197\7q\2\2\u0197\u0198\7y\2\2\u0198"+
		"\u0199\7u\2\2\u0199v\3\2\2\2\u019a\u019b\7v\2\2\u019b\u019c\7t\2\2\u019c"+
		"\u019d\7w\2\2\u019d\u019e\7g\2\2\u019ex\3\2\2\2\u019f\u01a0\7v\2\2\u01a0"+
		"\u01a1\7{\2\2\u01a1\u01a2\7r\2\2\u01a2\u01a3\7g\2\2\u01a3z\3\2\2\2\u01a4"+
		"\u01a5\7w\2\2\u01a5\u01a6\7p\2\2\u01a6\u01a7\7h\2\2\u01a7\u01a8\7q\2\2"+
		"\u01a8\u01a9\7n\2\2\u01a9\u01aa\7f\2\2\u01aa|\3\2\2\2\u01ab\u01ac\7x\2"+
		"\2\u01ac\u01ad\7c\2\2\u01ad\u01ae\7t\2\2\u01ae\u01af\7k\2\2\u01af\u01b0"+
		"\7c\2\2\u01b0\u01b1\7p\2\2\u01b1\u01b2\7v\2\2\u01b2~\3\2\2\2\u01b3\u01b4"+
		"\7y\2\2\u01b4\u01b5\7k\2\2\u01b5\u01b6\7v\2\2\u01b6\u01b7\7j\2\2\u01b7"+
		"\u0080\3\2\2\2\u01b8\u01b9\7\u00b7\2\2\u01b9\u0082\3\2\2\2\u01ba\u01bb"+
		"\7\61\2\2\u01bb\u01bc\7\61\2\2\u01bc\u01c0\3\2\2\2\u01bd\u01bf\n\5\2\2"+
		"\u01be\u01bd\3\2\2\2\u01bf\u01c2\3\2\2\2\u01c0\u01be\3\2\2\2\u01c0\u01c1"+
		"\3\2\2\2\u01c1\u01c8\3\2\2\2\u01c2\u01c0\3\2\2\2\u01c3\u01c5\7\17\2\2"+
		"\u01c4\u01c3\3\2\2\2\u01c4\u01c5\3\2\2\2\u01c5\u01c6\3\2\2\2\u01c6\u01c9"+
		"\7\f\2\2\u01c7\u01c9\7\2\2\3\u01c8\u01c4\3\2\2\2\u01c8\u01c7\3\2\2\2\u01c9"+
		"\u01ca\3\2\2\2\u01ca\u01cb\bB\2\2\u01cb\u0084\3\2\2\2\u01cc\u01cd\3\2"+
		"\2\2\u01cd\u01ce\3\2\2\2\u01ce\u01cf\bC\2\2\u01cf\u0086\3\2\2\2\u01d0"+
		"\u01d3\7a\2\2\u01d1\u01d3\5\3\2\2\u01d2\u01d0\3\2\2\2\u01d2\u01d1\3\2"+
		"\2\2\u01d3\u01db\3\2\2\2\u01d4\u01da\t\6\2\2\u01d5\u01d8\5\t\5\2\u01d6"+
		"\u01d8\5\3\2\2\u01d7\u01d5\3\2\2\2\u01d7\u01d6\3\2\2\2\u01d8\u01da\3\2"+
		"\2\2\u01d9\u01d4\3\2\2\2\u01d9\u01d7\3\2\2\2\u01da\u01dd\3\2\2\2\u01db"+
		"\u01d9\3\2\2\2\u01db\u01dc\3\2\2\2\u01dc\u0088\3\2\2\2\u01dd\u01db\3\2"+
		"\2\2\u01de\u01e6\7)\2\2\u01df\u01e5\t\7\2\2\u01e0\u01e3\5\t\5\2\u01e1"+
		"\u01e3\5\3\2\2\u01e2\u01e0\3\2\2\2\u01e2\u01e1\3\2\2\2\u01e3\u01e5\3\2"+
		"\2\2\u01e4\u01df\3\2\2\2\u01e4\u01e2\3\2\2\2\u01e5\u01e8\3\2\2\2\u01e6"+
		"\u01e4\3\2\2\2\u01e6\u01e7\3\2\2\2\u01e7\u01e9\3\2\2\2\u01e8\u01e6\3\2"+
		"\2\2\u01e9\u01ea\7)\2\2\u01ea\u008a\3\2\2\2\u01eb\u01ed\5\t\5\2\u01ec"+
		"\u01eb\3\2\2\2\u01ed\u01ee\3\2\2\2\u01ee\u01ec\3\2\2\2\u01ee\u01ef\3\2"+
		"\2\2\u01ef\u008c\3\2\2\2\u01f0\u01f2\t\b\2\2\u01f1\u01f0\3\2\2\2\u01f2"+
		"\u01f3\3\2\2\2\u01f3\u01f1\3\2\2\2\u01f3\u01f4\3\2\2\2\u01f4\u01f5\3\2"+
		"\2\2\u01f5\u01f6\bG\2\2\u01f6\u008e\3\2\2\2\u01f7\u01f8\t\t\2\2\u01f8"+
		"\u0090\3\2\2\2\u01f9\u01fa\13\2\2\2\u01fa\u0092\3\2\2\2\20\2\u0095\u01c0"+
		"\u01c4\u01c8\u01d2\u01d7\u01d9\u01db\u01e2\u01e4\u01e6\u01ee\u01f3\3\b"+
		"\2\2";
	public static final ATN _ATN =
		new ATNDeserializer().deserialize(_serializedATN.toCharArray());
	static {
		_decisionToDFA = new DFA[_ATN.getNumberOfDecisions()];
		for (int i = 0; i < _ATN.getNumberOfDecisions(); i++) {
			_decisionToDFA[i] = new DFA(_ATN.getDecisionState(i), i);
		}
	}
}