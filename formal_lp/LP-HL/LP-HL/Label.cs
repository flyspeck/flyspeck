using System;
using System.Collections.Generic;
using System.Linq;
using System.Text;

namespace LP_HL
{
    /// <summary>
    /// Full name of a variable or an inequality
    /// </summary>
    class Label : IComparable<Label>
    {
        // Main name
        public readonly string name;
        // Index
        public readonly string index;


        /// <summary>
        /// Default constructor
        /// </summary>
        public Label(string name, string index)
        {
            this.name = name;
            this.index = index;
        }


        /// <summary>
        /// Creates a new label with the given name and with the same
        /// index as in the given variable
        /// </summary>
        public Label(Label label, string newName)
        {
            this.name = newName;
            this.index = label.index;
        }


        /// <summary>
        /// A special label
        /// </summary>
        public static Label SpecialLabel = new Label("***", "");


        /// <summary>
        /// Parses a label
        /// </summary>
        public static Label ParseLabel(Scanner scanner)
        {
            Token t = scanner.nextToken();

            if (t.Type != TokenType.Identifier)
                throw new Exception("Identifier expected: " + t);

            String name = t.StringValue;

            StringBuilder str = new StringBuilder();
            t = scanner.peekToken();
            if (t.Type == TokenType.LParen)
            {
                // (
                scanner.nextToken();
                t = scanner.peekToken();
                if (t.Type != TokenType.RParen)
                {
                    while (true)
                    {
                        t = scanner.nextToken();

                        if (t.Type != TokenType.Identifier && t.Type != TokenType.Integer)
                            throw new Exception("Identifier or integer expected: " + t);

                        str.Append(t.StringValue);

                        // ) or ,
                        t = scanner.nextToken();
                        if (t.Type == TokenType.RParen)
                            break;

                        if (t.Type != TokenType.Comma)
                            throw new Exception(", expected: " + t);

                        str.Append(',');
                    }
                }
                else
                {
                    // )
                    scanner.nextToken();
                }
            }

            return new Label(name, str.ToString());
        }


        // ToString()
        public override string ToString()
        {
            if (index == "")
                return name;

            return name + "(" + index + ")";
        }


        public override bool Equals(object obj)
        {
            Label l2 = obj as Label;
            if (l2 == null)
                return false;

            return name == l2.name && index == l2.index;
        }


        public override int GetHashCode()
        {
            return name.GetHashCode() ^ index.GetHashCode();
        }

        public int CompareTo(Label other)
        {
            return this.ToString().CompareTo(other.ToString());
        }
    }
}
