using System;
using System.Collections.Generic;
using System.Linq;
using System.Text;

namespace LP_HL
{
    /// <summary>
    /// Types of tokens for lp files
    /// </summary>
    enum TokenType
    {
        Identifier,
        Integer, Double,
        String,
        Colon, Comma, Semicolon,
        Eq, Le, Ge,
        Plus, Minus,
        LParen, RParen,
        EOF
    }

    /// <summary>
    /// Represents a token for data files
    /// </summary>
    class Token
    {
        /// <summary>
        /// Token's type
        /// </summary>
        public TokenType Type { get; private set; }

        /// <summary>
        /// Value of the token as a string
        /// </summary>
        public string StringValue { get; private set; }

        /// <summary>
        /// Value of the token as an integer
        /// </summary>
        public int IntegerValue { get; private set; }


        /// <summary>
        /// Values of the token as a float number
        /// </summary>
        public double DoubleValue { get; private set; }

        /// <summary>
        /// File name
        /// </summary>
        public string FileName { get; private set; }

        /// <summary>
        /// Line number
        /// </summary>
        public int LineNumber { get; private set; }

        /// <summary>
        /// Column number
        /// </summary>
        public int ColNumber { get; private set; }


        /// <summary>
        /// Returns token's location
        /// </summary>
        public string Location
        {
            get
            {
                return FileName + ": " + (LineNumber + 1) + ", " + (ColNumber + 1);
            }
        }


        /// <summary>
        /// Creates a token with all parameters
        /// </summary>
        /// <param name="type"></param>
        /// <param name="value"></param>
        /// <param name="fname"></param>
        /// <param name="line"></param>
        /// <param name="col"></param>
        public Token(TokenType type, string value, string fname, int line, int col)
        {
            this.Type = type;
            this.StringValue = value;
            this.FileName = fname;
            this.LineNumber = line;
            this.ColNumber = col;

            if (type == TokenType.Integer)
            {
                this.IntegerValue = int.Parse(value);
                this.DoubleValue = (double)IntegerValue;
            }

            if (type == TokenType.Double)
            {
                this.DoubleValue = double.Parse(value);
            }
        }


        /// <summary>
        /// Creates a token without location
        /// </summary>
        /// <param name="?"></param>
        /// <param name="value"></param>
        public Token(TokenType type, string value) :
            this(type, value, null, 0, 0)
        {
        }


        /// <summary>
        /// Creates a token without value
        /// </summary>
        /// <param name="type"></param>
        /// <param name="fname"></param>
        /// <param name="line"></param>
        /// <param name="col"></param>
        public Token(TokenType type, string fname, int line, int col) :
            this(type, "", fname, line, col)
        {
        }


        /// <summary>
        /// Creates a token without value and location
        /// </summary>
        /// <param name="type"></param>
        public Token(TokenType type) :
            this(type, "", null, 0, 0)
        {
        }


        /// <summary>
        /// Converts the token into a string
        /// </summary>
        /// <returns></returns>
        public override string ToString()
        {
            StringBuilder str = new StringBuilder("Token[Type = ");
            str.Append(Type);
            str.Append("; Value = ");
            str.Append(StringValue);

            if (FileName != null)
            {
                str.Append("; Location = ");
                str.Append(Location);
            }

            str.Append("]");
            return str.ToString();
        }
    }
}
