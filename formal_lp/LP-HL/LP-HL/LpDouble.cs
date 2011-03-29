using System;
using System.Collections.Generic;
using System.Linq;
using System.Text;

namespace LP_HL
{
    /// <summary>
    /// Represents a number
    /// </summary>
    class LpNumber : IComparable<LpNumber>
    {
        // Minimal precision;
        public const decimal DecimalEps = 1e-10m;

        // value
        public readonly decimal value;

        /// <summary>
        /// Default constructor
        /// </summary>
        /// <param name="value"></param>
        public LpNumber(decimal value)
        {
            this.value = value;
        }

        /// <summary>
        /// Constructs a number from its string representation and with the given
        /// precision (precision = 0 means that the number should be read as is)
        /// </summary>
        /// <param name="value"></param>
        public LpNumber(double val, int precision)
        {
            value = (decimal)val;
            if (IsZero(precision))
            {
                value = 0;
            }
            else
            {
                if (precision <= 0)
                    return;

                value *= pow10[precision];
                value = Math.Round(value);
                value /= pow10[precision];
            }
        }

        /// <summary>
        /// Copy constructor
        /// </summary>
        /// <param name="num"></param>
        public LpNumber(LpNumber num) : this(num.value)
        {
        }

        /// <summary>
        /// Returns true if the value is zero
        /// (up to some precision)
        /// </summary>
        /// <param name="precision"></param>
        /// <returns></returns>
        public bool IsZero(int precision)
        {
            return Math.Abs(value) < DecimalEps;
        }


        /// <summary>
        /// ToString()
        /// </summary>
        /// <returns></returns>
        public override string ToString()
        {
            return value.ToString();
        }


        /// <summary>
        /// Table of powers of 10
        /// </summary>
        private static decimal[] pow10;


        /// <summary>
        /// Static initializer
        /// </summary>
        static LpNumber()
        {
            pow10 = new decimal[28];
            decimal p = 1;
            for (int i = 0; i < 28; i++)
            {
                pow10[i] = p;
                p *= 10;
            }
        }


        /// <summary>
        /// Rounds up a given number with the precision k digits
        /// </summary>
        /// <param name="v"></param>
        /// <param name="k"></param>
        /// <returns></returns>
        public static decimal RoundUp(decimal v, int k)
        {
//            if (v < 0)
//                return -RoundDown(-v, k);

            decimal m = pow10[k];
            v *= m;
            v = Math.Ceiling(v);
            return v / m;
        }


        /// <summary>
        /// Rounds down a given number with the precision k digits
        /// </summary>
        /// <param name="v"></param>
        /// <param name="k"></param>
        /// <returns></returns>
        public static decimal RoundDown(decimal v, int k)
        {
//            if (v < 0)
//                return -RoundUp(-v, k);
            decimal m = pow10[k];
            v *= m;
            v = Math.Floor(v);
            return v / m;
        }


        /// <summary>
        /// Rounds up the number such that the resulting number
        /// is greater or equal than the original number,
        /// and such that |original - rounded| &lt;= 1e-k
        /// </summary>
        /// <param name="precision"></param>
        public LpNumber RoundUp(int k)
        {
            return new LpNumber(RoundUp(value, k));
        }


        /// <summary>
        /// Rounds down the number such that the resulting number
        /// is less or equal than the original number,
        /// and such that |original - rounded| &lt;= 1e-k
        /// </summary>
        /// <param name="precision"></param>
        public LpNumber RoundDown(int k)
        {
            return new LpNumber(RoundDown(value, k));
        }


        /// <summary>
        /// Converts to a HOL string
        /// </summary>
        /// <param name="precision"></param>
        /// <returns></returns>
        public string ToHOLString(int precision)
        {
            StringBuilder str = new StringBuilder();
            decimal val = value;

            if (val < 0)
            {
                str.Append("-- ");
                val = -val;
            }

            str.Append('&');
            decimal mul = 1;
            for (int i = 0; i < precision; i++)
            {
                decimal t = val * mul;
                if (Math.Round(t) == t)
                    break;

                mul *= 10;
            }

            str.Append(Math.Round(val * mul));
            if (mul > 1)
            {
                str.Append(" / &");
                str.Append(mul);
            }

            return str.ToString();
        }


        /// <summary>
        /// Converts to a HOL explicit term
        /// </summary>
        /// <param name="precision"></param>
        /// <returns></returns>
        public string ToHOLExplicit2(int precision)
        {
            StringBuilder str = new StringBuilder();
            decimal val = value;

            str.Append("(");

            if (val < 0)
            {
                str.Append("negate (");
                val = -val;
            }
            
            str.Append("term_of_rat (num_of_string \"");

            decimal mul = 1;
            for (int i = 0; i < precision; i++)
            {
                decimal t = val * mul;
                if (Math.Round(t) == t)
                    break;

                mul *= 10;
            }

            str.Append(Math.Round(val * mul));
            str.Append('"');

            if (mul > 1)
            {
                str.Append(" // num_of_string \"");
                str.Append(mul);
                str.Append('"');
            }

            if (value < 0)
                str.Append(')');

            str.Append("))");

            return str.ToString();
        }


        /// <summary>
        /// Converts to a HOL explicit decimal term
        /// </summary>
        /// <param name="precision"></param>
        /// <returns></returns>
        public string ToHOLExplicit_old(int precision)
        {
            StringBuilder str = new StringBuilder();
            decimal val = value;

            str.Append("(");

            if (val < 0)
            {
                str.Append("negate (");
                val = -val;
            }


            decimal mul = 1;
            for (int i = 0; i < precision; i++)
            {
                decimal t = val * mul;
                if (Math.Round(t) == t)
                    break;

                mul *= 10;
            }

            if (mul == 1)
            {
                str.Append("term_of_rat (num_of_string \"");
                str.Append(Math.Round(val));
                str.Append("\")");
            }
            else
            {
                str.Append("mk_decimal (num_of_string \"");
                str.Append(Math.Round(val * mul));
                str.Append("\", num_of_string \"");
                str.Append(mul);
                str.Append("\")");
            }

            if (value < 0)
                str.Append(')');

            str.Append(')');

            return str.ToString();
        }


        /// <summary>
        /// Converts to a HOL explicit decimal term
        /// </summary>
        /// <param name="precision"></param>
        /// <returns></returns>
        public string ToHOLExplicit(int precision)
        {
            StringBuilder str = new StringBuilder();
            decimal val = value;

            str.Append("(");

            if (val < 0)
            {
                str.Append("negate (");
                val = -val;
            }

            if (Math.Round(val) != val)
                throw new Exception("Only integers can be used");

            if (val < Int64.MaxValue)
            {
                str.Append("mk_real_int64 ");
                str.Append(Math.Round(val));
                str.Append("L");
            }
            else
            {
                str.Append("mk_real_int (num_of_string \"");
                str.Append(Math.Round(val));
                str.Append("\")");
            }

            if (value < 0)
                str.Append(')');

            str.Append(')');

            return str.ToString();
        }



        /// <summary>
        /// Multiplication
        /// </summary>
        /// <param name="n1"></param>
        /// <param name="n2"></param>
        /// <returns></returns>
        public static LpNumber operator *(LpNumber n1, LpNumber n2)
        {
            return new LpNumber(n1.value * n2.value);
        }

        public static LpNumber operator *(LpNumber n1, decimal n2)
        {
            return new LpNumber(n1.value * n2);
        }

        public static LpNumber operator *(decimal n1, LpNumber n2)
        {
            return new LpNumber(n1 * n2.value);
        }

        /// <summary>
        /// Addition
        /// </summary>
        /// <param name="n1"></param>
        /// <param name="n2"></param>
        /// <returns></returns>
        public static LpNumber operator +(LpNumber n1, LpNumber n2)
        {
            return new LpNumber(n1.value + n2.value);
        }

        public static LpNumber operator +(LpNumber n1, decimal n2)
        {
            return new LpNumber(n1.value + n2);
        }

        public static LpNumber operator +(decimal n1, LpNumber n2)
        {
            return new LpNumber(n1 + n2.value);
        }

        /// <summary>
        /// Negation
        /// </summary>
        /// <param name="n"></param>
        /// <returns></returns>
        public static LpNumber operator -(LpNumber n)
        {
            return new LpNumber(-n.value);
        }

        /// <summary>
        /// Subtraction
        /// </summary>
        /// <param name="n1"></param>
        /// <param name="n2"></param>
        /// <returns></returns>
        public static LpNumber operator -(LpNumber n1, LpNumber n2)
        {
            return new LpNumber(n1.value - n2.value);
        }

        public static LpNumber operator -(LpNumber n1, decimal n2)
        {
            return new LpNumber(n1.value - n2);
        }

        public static LpNumber operator -(decimal n1, LpNumber n2)
        {
            return new LpNumber(n1 - n2.value);
        }


        /// <summary>
        /// IComparable implementation
        /// </summary>
        /// <param name="other"></param>
        /// <returns></returns>
        public int CompareTo(LpNumber other)
        {
            return value.CompareTo(other.value);
        }
    }
}
