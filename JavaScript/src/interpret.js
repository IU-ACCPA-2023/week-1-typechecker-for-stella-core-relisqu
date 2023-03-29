import antlr4 from 'antlr4';
import stellaLexer from './stella/stellaLexer.js';
import stellaParser from './stella/stellaParser.js';
import stellaParserListener from './stella/stellaParserListener.js';
import * as fs from 'fs';

class Visitor {
  visitChildren(ctx) {
    if (!ctx) {
      return;
    }

    if (ctx.children) {
      return ctx.children.map(child => {
        if (child.children && child.children.length != 0) {
          return child.accept(this);
        } else {
          return child.getText();
        }
      });
    }
  }
}

class stellaListener extends stellaParserListener {
    constructor() {
        super();
    }
   
    enterDecl(ctx) {}
    exitDecl(ctx) {}
    enterExpr(ctx) {}
    exitExpr(ctx) {}
}

class DeclPrinter extends stellaListener {
    // override default listener behavior
    exitDecl(ctx) {
        console.log("new declaration: " + ctx.p_1_3.text);
    }
}

var input = "";
if (process.argv.length <= 2) {
  input = fs.readFileSync('/dev/stdin').toString();
} else {
  input = fs.readFileSync(process.argv[2]).toString();
}
const chars = new antlr4.InputStream(input);
const lexer = new stellaLexer(chars);
const tokens = new antlr4.CommonTokenStream(lexer);
const parser = new stellaParser(tokens);
parser.buildParseTrees = true;
const tree = parser.start_Program();
const printer = new DeclPrinter();
antlr4.tree.ParseTreeWalker.DEFAULT.walk(printer, tree);
