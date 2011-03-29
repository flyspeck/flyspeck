using System;
using System.Collections.Generic;
using System.Linq;
using System.Text;

namespace LP_HL
{
    /// <summary>
    /// An inequality
    /// </summary>
    class Inequality
    {
        // Identifier (name)
        public Label Id { get; private set; }

        public enum IneqType { Eq, Le, Ge };

        // Changes whenever the inequaility is multiplied by a negative constant
        public bool NegFlag { get; private set; }

        // Type of the (in)equality
        public readonly IneqType type;

        // RHS
        public readonly LpNumber rhs;


        // LHS
        public readonly LinearFunction lhs;


        // Marginal value (multiplier)
        public LpNumber Marginal { get; set; }


        /// <summary>
        /// Private constructor
        /// </summary>
        private Inequality(Label id, IneqType type, LinearFunction lhs, LpNumber rhs, bool negFlag)
        {
            this.Id = id;
            this.type = type;
            this.lhs = lhs;
            this.rhs = rhs;
            this.NegFlag = negFlag;
        }


        /// <summary>
        /// Returns the equality 0 = 0
        /// </summary>
        public static Inequality Zero()
        {
            Label id = new Label("ZERO", "");
            LinearFunction lhs = new LinearFunction(new List<decimal>(), new List<string>());
            LpNumber rhs = new LpNumber(0);
            Inequality ineq = new Inequality(id, IneqType.Eq, lhs, rhs, false);

            return ineq;
        }



        /// <summary>
        /// ToString()
        /// </summary>
        /// <returns></returns>
        public override string ToString()
        {
            StringBuilder str = new StringBuilder(Id.ToString());
            str.Append(": ");
            str.Append(lhs);
            switch (type)
            {
                case IneqType.Eq:
                    str.Append(" = ");
                    break;

                case IneqType.Le:
                    str.Append(" <= ");
                    break;

                case IneqType.Ge:
                    str.Append(" >= ");
                    break;
            }

            str.Append(rhs);
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

            str.Append(lhs.ToHOLString(precision, vars));

            switch (type)
            {
                case IneqType.Eq:
                    // An equality becomes an inequality
                    str.Append(" <= ");
                    break;

                case IneqType.Le:
                    str.Append(" <= ");
                    break;

                case IneqType.Ge:
                    str.Append(" >= ");
                    break;
            }

            str.Append(rhs.ToHOLString(precision));
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

            switch (type)
            {
                case IneqType.Eq:
                    // Eq becomes Le
                    str.Append("mk_le_ineq ");
                    break;

                case IneqType.Le:
                    str.Append("mk_le_ineq ");
                    break;

                case IneqType.Ge:
                    str.Append("mk_ge_ineq ");
                    break;
            }

            str.Append(lhs.ToHOLExplicit(precision, vars));
            str.Append(rhs.ToHOLExplicit(precision));

            return str.ToString();
        }


        /// <summary>
        /// Rounds the coefficients in the inequality.
        /// Does not work for inequalities of type Ge.
        /// Does not change inequalities of type Eq
        /// </summary>
        /// <returns></returns>
        public Inequality Round(int precision)
        {
            if (type == IneqType.Ge)
                throw new Exception("Cannot round Ge inequalities");

//            if (type == IneqType.Eq)
//                return this;
            if (type == IneqType.Eq)
            {
//                if (rhs.RoundUp(precision).value != rhs.value)
//                    Console.Error.WriteLine("Rounding an equality: " + this);
            }

            return new Inequality(Id, type, lhs.RoundDown(precision), rhs.RoundUp(precision), NegFlag);
        }


        /// <summary>
        /// Multiplication
        /// </summary>
        /// <param name="ineq"></param>
        /// <param name="n"></param>
        /// <returns></returns>
        public static Inequality operator *(Inequality ineq, decimal n)
        {
            IneqType type = ineq.type;
            bool newNegFlag = ineq.NegFlag;

            if (n < 0)
            {
                newNegFlag = !newNegFlag;

                if (type == IneqType.Le)
                    type = IneqType.Ge;
                else if (type == IneqType.Ge)
                    type = IneqType.Le;
            }

            return new Inequality(ineq.Id, type, ineq.lhs * n, ineq.rhs * n, newNegFlag);
        }


        /// <summary>
        /// Addition (works only for Le and Eq)
        /// </summary>
        /// <param name="i1"></param>
        /// <param name="i2"></param>
        /// <returns></returns>
        public static Inequality operator +(Inequality i1, Inequality i2)
        {
            if (i1.type == IneqType.Ge || i2.type == IneqType.Ge)
                throw new Exception("Cannot add inequalities of type Ge");

            return new Inequality(Label.SpecialLabel, IneqType.Le, i1.lhs + i2.lhs, i1.rhs + i2.rhs, false);
        }


        /// <summary>
        /// Negation
        /// </summary>
        /// <param name="i1"></param>
        /// <returns></returns>
        public static Inequality operator -(Inequality i1)
        {
            return i1 * (-1);
        }


        /// <summary>
        /// Creates a lower bound inequality for a variable
        /// </summary>
        /// <param name="var"></param>
        /// <returns></returns>
        public static Inequality FromLowerBound(Variable var)
        {
            Inequality ineq = new Inequality(new Label(var.Name, var.Name.name + "_lo"), 
                    IneqType.Ge, new LinearFunction(var), new LpNumber(var.LBound), false);

            return ineq;
        }


        /// <summary>
        /// Creates an upper bound inequality for a variable
        /// </summary>
        /// <param name="var"></param>
        /// <returns></returns>
        public static Inequality FromUpperBound(Variable var)
        {
            Inequality ineq = new Inequality(new Label(var.Name, var.Name.name + "_hi"), 
                    IneqType.Le, new LinearFunction(var), new LpNumber(var.UBound), false);

            return ineq;
        }


        /// <summary>
        /// Parses an inequality
        /// </summary>
        /// <param name="scanner"></param>
        /// <returns></returns>
        public static Inequality ParseInequality(Scanner scanner)
        {
            Token t;
            // Identifier
            Label id = Label.ParseLabel(scanner);

            // :
            t = scanner.nextToken();
            if (t.Type != TokenType.Colon)
                throw new Exception(": expected: " + t);

            // lhs
            LinearFunction lhs = LinearFunction.ParseFunction(scanner);

            // type
            t = scanner.nextToken();
            IneqType type;

            switch (t.Type)
            {
                case TokenType.Le:
                    type = IneqType.Le;
                    break;

                case TokenType.Ge:
                    type = IneqType.Ge;
                    break;

                case TokenType.Eq:
                    type = IneqType.Eq;
                    break;

                default:
                    throw new Exception("<=, =>, or = expected: " + t);
            }

            // rhs
            t = scanner.nextToken();

            if (t.Type != TokenType.Integer && t.Type != TokenType.Double)
                throw new Exception("A number is expected: " + t);

            LpNumber rhs = new LpNumber(decimal.Parse(t.StringValue));

            return new Inequality(id, type, lhs, rhs, false);
        }
    }
}
