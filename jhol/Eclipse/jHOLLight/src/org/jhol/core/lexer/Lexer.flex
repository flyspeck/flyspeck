package org.jhol.core.lexer;

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
        StringBuffer string = new StringBuffer();

        private Token lastToken;

        public Token peekToken() throws java.io.IOException {
                if (lastToken != null)
                        return lastToken;
                else
                        return lastToken = get_token();
        }

        public Token nextToken() throws java.io.IOException {
                if (lastToken != null) {
                        Token tmp = lastToken;
                        lastToken = null;
                        return tmp;
                }

                return get_token();
        }
%}
%eofval{
    return new Token(TokenType.EOF);
%eofval}

LineTerminator = \r|\n|\r\n
InputCharacter = [^\r\n]

WhiteSpace = [ \t\f]

IdentifierSymbol = [a-zA-Z]

Identifier = {IdentifierSymbol} ({IdentifierSymbol} | [_0-9])*

StringCharacter = [^\r\n\"\\]

%state STRING

%%

<YYINITIAL> {
          /* separators */
        "(" { return new Token(TokenType.LPAR); }
        ")" { return new Token(TokenType.RPAR); }
        "[" { return new Token(TokenType.LBRACK); }
        "]" { return new Token(TokenType.RBRACK); }
        "," { return new Token(TokenType.COMMA); }
		
		/* keywords */
		"Tyapp" { return new Token(TokenType.Tyapp); }
		"Tyvar" { return new Token(TokenType.Tyvar); }
		"Var" { return new Token(TokenType.Var); }
		"Const" { return new Token(TokenType.Const); }
		"Comb" { return new Token(TokenType.Comb); }
		"Abs" { return new Token(TokenType.Abs); }
		

        /* string literal */
        \"    { yybegin(STRING); string.setLength(0); }

        {WhiteSpace}        {}
        {LineTerminator}        {}

        {Identifier} { return new Token(TokenType.IDENTIFIER, yytext()); }
}

<STRING> {
          \"  { yybegin(YYINITIAL); return new Token(TokenType.STRING, string.toString()); }

  {StringCharacter}+             { string.append( yytext() ); }

  /* escape sequences */
/*  "\\b"                          { string.append( '\b' ); }
  "\\t"                          { string.append( '\t' ); }
  "\\n"                          { string.append( '\n' ); }
  "\\f"                          { string.append( '\f' ); }
  "\\r"                          { string.append( '\r' ); }
  "\\\""                         { string.append( '\"' ); }
  "\\'"                          { string.append( '\'' ); }
  "\\\\"                         { string.append( '\\' ); } */
}

. { System.err.println("Illegal character: "+yytext()); }
