using System;
using System.Collections.Generic;
using System.Linq;
using System.Text;

namespace LP_HL
{
    // Represents a term
    class Term : IComparable<Term>
    {
        // Coefficient
        public readonly LpNumber c;

        // Variable
        public readonly Label varName;

        /// <summary>
        /// Default constructor
        /// </summary>
        /// <param name="c"></param>
        /// <param name="varName"></param>
        public Term(LpNumber c, Label varName)
        {
            this.c = c;
            this.varName = varName;
        }


        /// <summary>
        /// Copy constructor
        /// </summary>
        /// <param name="t"></param>
        public Term(Term t)
        {
            this.c = t.c;
            this.varName = t.varName;
        }


        /// <summary>
        /// Rounds down the term (it is assumed that var >= 0)
        /// </summary>
        /// <returns></returns>
        public Term RoundDown(int precision)
        {
            return new Term(c.RoundDown(precision), varName);
        }


        /// <summary>
        /// ToString()
        /// </summary>
        /// <returns></returns>
        public override string ToString()
        {
            StringBuilder str = new StringBuilder();

            if (c.value >= 0)
                str.Append(" + ");
            else
                str.Append(" - ");

            if (Math.Abs(c.value) != 1)
                str.Append(c.value);

            str.Append(varName);
            return str.ToString();
        }


        /// <summary>
        /// Converts to a HOL string
        /// </summary>
        /// <param name="precision"></param>
        /// <returns></returns>
        public string ToHOLString(int precision, VariableCollection vars)
        {
            StringBuilder str = new StringBuilder();
            if (c.value == 0)
                return "";

            str.Append(c.ToHOLString(precision));
            str.Append(" * ");
            str.Append(vars[varName]);

            return str.ToString();
        }


        /// <summary>
        /// Converts to a HOL term
        /// </summary>
        /// <param name="precision"></param>
        /// <returns></returns>
        public string ToHOLExplicit(int precision, VariableCollection vars)
        {
            StringBuilder str = new StringBuilder();
            if (c.value == 0)
                return "";

            str.Append("(mk_term ");
            str.Append(c.ToHOLExplicit(precision));
            str.Append('"' + vars[varName].ToString() + '"');
            str.Append(')');

            return str.ToString();
        }


        /// <summary>
        /// Parses a term
        /// </summary>
        /// <param name="scanner"></param>
        /// <returns></returns>
        public static Term ParseTerm(Scanner scanner)
        {
            Token t = scanner.nextToken();
            bool negative = false;
            decimal c;
            Label varName;

            // Sign
            if (t.Type == TokenType.Minus)
            {
                negative = true;
            }
            else if (t.Type != TokenType.Plus)
            {
                throw new Exception("+ or - expected: " + t);
            }

            t = scanner.peekToken();

            // Coefficient
            if (t.Type == TokenType.Integer || t.Type == TokenType.Double)
            {
                // number
                scanner.nextToken();
                c = decimal.Parse(t.StringValue);
            }
            else
            {
                c = 1;
            }

            if (negative)
                c = -c;

            // Variable
            varName = Label.ParseLabel(scanner);

            return new Term(new LpNumber(c), varName);
        }


        /// <summary>
        /// Multiplication
        /// </summary>
        /// <param name="t1"></param>
        /// <param name="n"></param>
        /// <returns></returns>
        public static Term operator *(Term t1, decimal n)
        {
            return new Term(t1.c * n, t1.varName);
        }

        public static Term operator *(decimal n, Term t1)
        {
            return new Term(n * t1.c, t1.varName);
        }

        /// <summary>
        /// IComparable implementation
        /// </summary>
        /// <param name="other"></param>
        /// <returns></returns>
        public int CompareTo(Term other)
        {
            int r = varName.CompareTo(other.varName);
//            if (r == 0)
//                return c.CompareTo(other.c);
//            else
            // We are interested in varName only
            return r;
        }
    }


    /// <summary>
    /// A linear function in the form sum_i c[i] * x[i]
    /// </summary>
    class LinearFunction
    {

        // Terms
        private List<Term> terms;


        /// <summary>
        /// Protected constructor
        /// </summary>
        protected LinearFunction()
        {
            terms = new List<Term>();
        }


        /// <summary>
        /// Creates a linear function from explicit data
        /// </summary>
        /// <param name="cs"></param>
        /// <param name="vars"></param>
        public LinearFunction(List<decimal> cs, List<string> vars) : this()
        {
            for (int i = 0; i < cs.Count; i++)
            {
                Label label = new Label(Label.SpecialLabel, vars[i]);
                terms.Add(new Term(new LpNumber(cs[i]), label));
            }
        }


        /// <summary>
        /// Creates a linear function from a variable
        /// </summary>
        /// <param name="var"></param>
        public LinearFunction(Variable var)
            : this()
        {
            terms.Add(new Term(new LpNumber(1), var.Name));
        }


        /// <summary>
        /// Rounds down the linear function
        /// </summary>
        /// <param name="precision"></param>
        /// <returns></returns>
        public LinearFunction RoundDown(int precision)
        {
            LinearFunction f = new LinearFunction();

            foreach (var term in terms)
            {
                f.terms.Add(term.RoundDown(precision));
            }

            return f;
        }


        /// <summary>
        /// Terms
        /// </summary>
        /// <returns></returns>
        public IEnumerable<Term> Terms
        {
            get
            {
                for (int i = 0; i < terms.Count; i++)
                    yield return terms[i];
            }
        }


        /// <summary>
        /// ToString()
        /// </summary>
        /// <returns></returns>
        public override string ToString()
        {
            StringBuilder str = new StringBuilder();

            foreach (var term in terms)
            {
                str.Append(term);
            }

            return str.ToString();
        }


        /// <summary>
        /// Converts to a HOL string
        /// </summary>
        /// <param name="precision"></param>
        /// <returns></returns>
        public string ToHOLString(int precision, VariableCollection vars)
        {
            StringBuilder str = new StringBuilder();
            bool first = true;

            foreach (Term term in terms)
            {
                string t = term.ToHOLString(precision, vars);
                if (t == "")
                    continue;

                if (!first)
                    str.Append(" + ");
                str.Append(t);
                first = false;
            }

            return str.ToString();
        }


        /// <summary>
        /// Converts to a HOL term
        /// </summary>
        /// <param name="precision"></param>
        /// <returns></returns>
        public string ToHOLExplicit(int precision, VariableCollection vars)
        {
            StringBuilder str = new StringBuilder();
            str.Append("(mk_linear [");

            foreach (Term term in terms)
            {
                str.Append(term.c.ToHOLExplicit(precision));
                str.Append("; ");
            }

            str.Append("] [");
            foreach (Term term in terms)
            {
                if (vars != null)
                    str.Append('"' + vars[term.varName].ToString() + '"');
                else
                    str.Append("\"" + term.varName.ToString() + '"');
                str.Append("; ");
            }

            str.Append("])");

            return str.ToString();
        }


        /// <summary>
        /// Parses a linear function
        /// </summary>
        /// <param name="scanner"></param>
        /// <returns></returns>
        public static LinearFunction ParseFunction(Scanner scanner)
        {
            LinearFunction f = new LinearFunction();
            Token t;

            while (true)
            {
                t = scanner.peekToken();
                if (t.Type != TokenType.Plus && t.Type != TokenType.Minus)
                    break;

                Term term = Term.ParseTerm(scanner);
                f.terms.Add(term);
            }

            return f;
        }


        /// <summary>
        /// Multiplication
        /// </summary>
        /// <param name="f"></param>
        /// <param name="n"></param>
        /// <returns></returns>
        public static LinearFunction operator *(LinearFunction f, decimal n)
        {
            LinearFunction result = new LinearFunction();

            foreach (var term in f.terms)
            {
                result.terms.Add(term * n);
            }

            return result;
        }


        public static LinearFunction operator *(decimal n, LinearFunction f)
        {
            LinearFunction result = new LinearFunction();

            foreach (var term in f.terms)
            {
                result.terms.Add(term * n);
            }

            return result;
        }

        /// <summary>
        /// Negation
        /// </summary>
        /// <param name="f"></param>
        /// <returns></returns>
        public static LinearFunction operator -(LinearFunction f)
        {
            return f * (-1);
        }

        /// <summary>
        /// Addition
        /// </summary>
        /// <param name="f1"></param>
        /// <param name="f2"></param>
        /// <returns></returns>
        public static LinearFunction operator +(LinearFunction f1, LinearFunction f2)
        {
            f1.terms.Sort();
            f2.terms.Sort();

            LinearFunction f = new LinearFunction();

            int n1 = f1.terms.Count;
            int n2 = f2.terms.Count;
            int index1 = 0, index2 = 0;

            while (index1 < n1 && index2 < n2)
            {
                Term t1 = f1.terms[index1];
                Term t2 = f2.terms[index2];

                int r = t1.CompareTo(t2);
                if (r == 0)
                {
                    LpNumber n = t1.c + t2.c;
                    if (n.value != 0)
                        f.terms.Add(new Term(n, t1.varName));
                    index1++;
                    index2++;
                }
                else if (r > 0)
                {
                    f.terms.Add(t2);
                    index2++;
                }
                else
                {
                    f.terms.Add(t1);
                    index1++;
                }
            }

            for (int i = index1; i < n1; i++)
            {
                f.terms.Add(f1.terms[i]);
            }

            for (int i = index2; i < n2; i++)
            {
                f.terms.Add(f2.terms[i]);
            }

            return f;
        }

        /// <summary>
        /// Subtraction
        /// </summary>
        /// <param name="f1"></param>
        /// <param name="f2"></param>
        /// <returns></returns>
        public static LinearFunction operator -(LinearFunction f1, LinearFunction f2)
        {
            return f1 + (-f2);
        }
    }
}
