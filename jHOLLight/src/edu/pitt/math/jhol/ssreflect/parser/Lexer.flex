package edu.pitt.math.jhol.ssreflect.parser;


%%
%function get_token
%type Token
%eofval{
        return new Token(TokenType.EOF);
%eofval}
%eofclose

%char
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
    return new Token(TokenType.EOF, yychar, yyline, yycolumn);
%eofval}

LineTerminator = \r|\n|\r\n
InputCharacter = [^\r\n]

WhiteSpace = [ \t\f]

IdentifierSymbol = [a-zA-Z]
IdentifierSymbol2 = {IdentifierSymbol} | [_'0-9]

Identifier = {IdentifierSymbol} {IdentifierSymbol2}*
FullIdentifier = {Identifier} ([.]{Identifier}+)*

Integer = [-]? [0-9]+

RawEndChars = [`]

//StringCharacter = [^\r\n\"\\]
//StringCharacter = [^\"\\]
StringCharacter = [^\"]

%state STRING
%state RAW

%%

<YYINITIAL> {
          /* separators */
        "(" { return new Token(TokenType.LPAR, yychar, yyline, yycolumn); }
        ")" { return new Token(TokenType.RPAR, yychar, yyline, yycolumn); }
        "[" { return new Token(TokenType.LBRACK, yychar, yyline, yycolumn); }
        "]" { return new Token(TokenType.RBRACK, yychar, yyline, yycolumn); }
        "{" { return new Token(TokenType.LBRACE, yychar, yyline, yycolumn); }
        "}" { return new Token(TokenType.RBRACE, yychar, yyline, yycolumn); }
		"`" { return new Token(TokenType.BACK_QUOTE, yychar, yyline, yycolumn); }
        "," { return new Token(TokenType.COMMA, yychar, yyline, yycolumn); }
		";" { return new Token(TokenType.SEMICOLON, yychar, yyline, yycolumn); }
		"*" { return new Token(TokenType.STAR, yychar, yyline, yycolumn); }
		":" { return new Token(TokenType.COLON, yychar, yyline, yycolumn); }
		"=>" { return new Token(TokenType.ARROW, yychar, yyline, yycolumn); }
		"/" { return new Token(TokenType.SLASH, yychar, yyline, yycolumn); }
		"-" { return new Token(TokenType.DASH, yychar, yyline, yycolumn); }
		":=" { return new Token(TokenType.ASSIGN, yychar, yyline, yycolumn); }
		
		/* keywords */
		"//" { return new Token(TokenType.TRIV, yychar, yyline, yycolumn); }
		"/=" { return new Token(TokenType.SIMP, yychar, yyline, yycolumn); }
		"//=" { return new Token(TokenType.TRIV_SIMP, yychar, yyline, yycolumn); }
		"_" { return new Token(TokenType.UNDERSCORE, yychar, yyline, yycolumn); }
		"." { return new Token(TokenType.PERIOD, yychar, yyline, yycolumn); }
		"@" { return new Token(TokenType.AT, yychar, yyline, yycolumn); }
		"!" { return new Token(TokenType.EXCLAMATION, yychar, yyline, yycolumn); }
		"?" { return new Token(TokenType.QUESTION, yychar, yyline, yycolumn); }

        /* string literal */
        \"    { yybegin(STRING); string.setLength(0); }

        {WhiteSpace}        {}
        {LineTerminator}        {}

		{Integer} { return new Token(TokenType.INTEGER, yytext(), yychar, yyline, yycolumn); }
        {FullIdentifier} { return new Token(TokenType.IDENTIFIER, yytext(), yychar, yyline, yycolumn); }
}

<STRING> 
{
  /* escape sequences */
/*  "\\b"                          { string.append( '\b' ); }
  "\\t"                          { string.append( '\t' ); }
  "\\n"                          { string.append( '\n' ); }
  "\\f"                          { string.append( '\f' ); }
  "\\r"                          { string.append( '\r' ); }
  "\\\""                         { string.append( '\"' ); }
  "\\'"                          { string.append( '\'' ); }
  "\\\\"                         { string.append( '\\' ); }*/ 

  \"  { yybegin(YYINITIAL); return new Token(TokenType.STRING, string.toString(), yychar, yyline, yycolumn); }

  {StringCharacter}+   { string.append( yytext() ); }
}

<RAW>
{
	{RawEndChars}	{ yybegin(YYINITIAL); return new Token(TokenType.STRING, string.toString(), yychar, yyline, yycolumn); }
	{StringCharacter}+	{ string.append( yytext() ); }
}

. { System.err.println("Illegal character: "+yytext()); }
