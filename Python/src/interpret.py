import sys
from antlr4 import *
from stella.stellaParser import stellaParser
from stella.stellaLexer import stellaLexer

class stellaListener(ParseTreeListener):
    def enterDecl(self, ctx):
        pass
    def exitDecl(self, ctx):
        pass
    def enterExpr(self, ctx):
        pass
    def exitExpr(self, ctx):
        pass

class DeclPrinter(stellaListener):
    def exitDecl(self, ctx):
        print("new declaration:", ctx.p_1_3.text)

def main(argv):
    if len(argv) > 1:
        input_stream = FileStream(argv[1])
    else:
        input_stream = StdinStream()
    lexer = stellaLexer(input_stream)
    stream = CommonTokenStream(lexer)
    parser = stellaParser(stream)
    tree = parser.start_Program()
    # print(tree.toStringTree(recog=parser))

    printer = DeclPrinter()
    walker = ParseTreeWalker()
    walker.walk(printer, tree)
 
if __name__ == '__main__':
    main(sys.argv)
