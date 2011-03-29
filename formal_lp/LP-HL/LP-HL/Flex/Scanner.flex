using System;
using System.Collections.Generic;
using System.Linq;
using System.Text;
using System.IO;

namespace LP_HL
{

%%
%function get_token
%type Token
%eofval{
        return new Token(TokenType.EOF);
%eofval}
%eofclose

%line
%column

%class Scanner
%{
      private StringBuilder str = new StringBuilder();

        private string fname;

        private Queue<Token> buffer = new Queue<Token>();

        public Scanner(TextReader @in, string fname)
            : this(@in)
        {
            this.fname = fname;
        }

        private void FillBuffer(int n)
        {
            for (int i = buffer.Count; i < n; i++)
            {
                buffer.Enqueue(get_token());
            }
        }


        public Token peekToken()
        {
            FillBuffer(1);
            return buffer.Peek();
        }

        public Token peekToken(int n)
        {
            FillBuffer(n + 1);
            return buffer.ElementAt(n);
        }

        public Token nextToken()
        {
            FillBuffer(1);
            return buffer.Dequeue();
        }

%}
%eofval{
    return new Token(TokenType.EOF);
%eofval}


LineTerminator = \r|\n|\r\n
InputCharacter = [^\r\n]

WhiteSpace = [ \t\f]

Comment = "\\*" ({InputCharacter} | {LineTerminator})* "*\\"
IdentifierSymbol = [a-zA-Z]
SpecialSymbol = [*\^]

Identifier = {IdentifierSymbol} ({IdentifierSymbol} | [_0-9-])*

IntegerLiteral = [-]? [0-9]+
StringCharacter = [^\"]

DoubleLiteral = [-]? ({FLit1}|{FLit2}|{FLit3}) {Exponent}?
FLit1    = [0-9]+ \. [0-9]*
FLit2    = \. [0-9]+
FLit3    = [0-9]+
Exponent = [eE] [+-]? [0-9]+



%state STRING

%%

<YYINITIAL> {
    /* special */
    ":" { return new Token(TokenType.Colon, ":", fname, yyline, yycolumn); }
    "," { return new Token(TokenType.Comma, ",", fname, yyline, yycolumn); }
    ";" { return new Token(TokenType.Semicolon, ";", fname, yyline, yycolumn); }

	/* operators */
    "=" { return new Token(TokenType.Eq, "=", fname, yyline, yycolumn); }
    "+" { return new Token(TokenType.Plus, "+", fname, yyline, yycolumn); }
    "-" { return new Token(TokenType.Minus, "-", fname, yyline, yycolumn); }
    "<=" { return new Token(TokenType.Le, "<=", fname, yyline, yycolumn); }
    ">=" { return new Token(TokenType.Ge, ">=", fname, yyline, yycolumn); }

    /* parentheses */
    "(" { return new Token(TokenType.LParen, "(", fname, yyline, yycolumn); }
    ")" { return new Token(TokenType.RParen, ")", fname, yyline, yycolumn); }

    /* string literal */
    \"    { yybegin(STRING); str.Length = 0; }

    /* numbers */
    {IntegerLiteral} { return new Token(TokenType.Integer, yytext(), fname, yyline, yycolumn); }
    {DoubleLiteral} { return new Token(TokenType.Double, yytext(), fname, yyline, yycolumn); }
	

    {Comment}        {}
    {WhiteSpace}        {}
    {LineTerminator}        {}
    {Identifier} { return new Token(TokenType.Identifier, yytext(), fname, yyline, yycolumn); }
}

<STRING> {
    \"  { yybegin(YYINITIAL); return new Token(TokenType.String, str.ToString(), fname, yyline, yycolumn); }

    {StringCharacter}+             { str.Append( yytext() ); }

}

. { Console.WriteLine("Illegal character: " + yytext()); }

%%
}
