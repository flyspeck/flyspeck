using System;
using System.Collections.Generic;
using System.Linq;
using System.Text;
using System.IO;

namespace LP_HL
{
    // Linear program
    partial class LP
    {
        // Original constraints
        private List<Inequality> originalIneqs;

        // Objective
        private LinearFunction objective;

        // The upper bound of the objective function
        private LpNumber upperBound;

        // Variables (with bounds)
        private VariableCollection vars;


        // Constraints
        private List<Inequality> ineqs;
        // Marginals
//        private List<LpNumber> ineqMarginals;

        // Inequalities from variables
        private List<Inequality> varIneqs;
        // Marginals
//        private List<LpNumber> varIneqMarginals;


        /// <summary>
        /// Private constructor
        /// </summary>
        private LP()
        {
            originalIneqs = new List<Inequality>();
            vars = new VariableCollection();
        }


        /// <summary>
        /// Processes all inequalities based on the given solution
        /// </summary>
        /// <param name="sol"></param>
        /// <param name="precision"></param>
        /// <returns></returns>
        public bool SetSolution(LPSolution sol, int precision)
        {
            if (sol.NumberOfVariables != vars.Number)
                throw new Exception("Inconsistent number of variables");

            if (sol.NumberOfConstraints != originalIneqs.Count)
                throw new Exception("Inconsistent number of constraints");
            
            ineqs = new List<Inequality>();
//            ineqMarginals = new List<LpNumber>();

            // Constraints
            for (int i = 0; i < sol.NumberOfConstraints; i++)
            {
                LpNumber m = sol.ConstraintMarginals[i];
                if (m.IsZero(precision))
                    continue;

                Inequality ineq = originalIneqs[i];

                if (m.value < 0)
                {
                    ineq = -ineq;
                    m = -m;
                }

                ineq = ineq.Round(precision);
                ineq.Marginal = m;
                ineqs.Add(ineq);
//                ineqMarginals.Add(m);
            }

            // Variables
            List<Inequality> tmpIneqs = new List<Inequality>();

            for (int i = 0; i < sol.NumberOfVariables; i++)
            {
                Variable var = vars[i];
                LpNumber m = sol.VariableMarginals[i];
                if (m.IsZero(precision))
                    continue;

                Inequality ineq;

                if (m.value < 0)
                {
                    var.LMarginal = -m;
                    ineq = -Inequality.FromLowerBound(var);
                    ineq = ineq.Round(precision) * (-m.value);
                }
                else
                {
                    var.UMarginal = m;
                    ineq = Inequality.FromUpperBound(var);
                    ineq = ineq.Round(precision) * m.value;
                }

                tmpIneqs.Add(ineq);
            }


            // Compute additional inequality
//            Inequality sum1 = ineqs[0] * ineqs[0].Marginal.value; //ineqMarginals[0].value;
            Inequality sum1 = Inequality.Zero();

            for (int i = 0; i < ineqs.Count; i++)
            {
                sum1 += ineqs[i] * ineqs[i].Marginal.value; //ineqMarginals[i].value;
            }

            Inequality sum2 = sum1;

            for (int i = 0; i < tmpIneqs.Count; i++)
            {
                sum2 += tmpIneqs[i];
            }

            // df
            LinearFunction df = objective - sum2.lhs;

            // Compute corrections for marginals
            foreach (var term in df.Terms)
            {
                LpNumber c = term.c;
                if (c.value < 0)
                {
                    vars[term.varName].LMarginal -= c;
                }
                else
                {
                    vars[term.varName].UMarginal += c;
                }
            }

            // Verification
            LpNumber sum = sum1.rhs;
            for (int i = 0; i < vars.Number; i++)
            {
                Variable var = vars[i];
                if (!var.LMarginal.IsZero(precision))
                {
                    sum -= var.LMarginal * LpNumber.RoundDown(var.LBound, precision);
                }

                if (!var.UMarginal.IsZero(precision))
                {
                    sum += var.UMarginal * LpNumber.RoundUp(var.UBound, precision);
                }
            }

            LpNumber eps = sol.UpperBound - sum;

            Console.WriteLine("eps = {0}", eps);

            if (eps.value < 0)
                return false;

            // Set the upper bound
            upperBound = sol.UpperBound;

            // Generate inequalities for variables
            Console.Write("Generating inequalities for variables...");
            varIneqs = new List<Inequality>();
//            varIneqMarginals = new List<LpNumber>();

            for (int i = 0; i < vars.Number; i++)
            {
                Variable var = vars[i];
                Inequality ineq;

                if (!var.LMarginal.IsZero(precision))
                {
                    ineq = -Inequality.FromLowerBound(var);
                    ineq = ineq.Round(precision);
                    ineq.Marginal = var.LMarginal;
                    varIneqs.Add(ineq);
//                    varIneqMarginals.Add(var.LMarginal);
                }

                if (!var.UMarginal.IsZero(precision))
                {
                    ineq = Inequality.FromUpperBound(var);
                    ineq = ineq.Round(precision);
                    ineq.Marginal = var.UMarginal;
                    varIneqs.Add(ineq);
//                    varIneqMarginals.Add(var.UMarginal);
                }
            }
            Console.WriteLine("done");

            return true;
        }


 

        /// <summary>
        /// Parses a bound of a variable
        /// </summary>
        /// <param name="scanner"></param>
        /// <param name="lp"></param>
        private static void ParseBound(Scanner scanner, LP lp)
        {
            Label varName;

            // TODO: wrong way of dealing with free variables
            // because the name of a variable could be more complicated
            // than just one identifier
            Token t = scanner.peekToken(1);
            if (t.Type == TokenType.Identifier && t.StringValue == "free")
            {
                // name
                varName = Label.ParseLabel(scanner);
                lp.vars.AddVariable(varName);

                // free
                t = scanner.nextToken();
                return;
            }

            // Lower bound
            t = scanner.nextToken();
            if (t.Type != TokenType.Integer && t.Type != TokenType.Double)
                throw new Exception("A number is expected: " + t);

            decimal low = decimal.Parse(t.StringValue);

            // <=
            t = scanner.nextToken();
            if (t.Type != TokenType.Le)
                throw new Exception("<= expected: " + t);

            // Variable
            varName = Label.ParseLabel(scanner);

            // <=
            t = scanner.nextToken();
            if (t.Type != TokenType.Le)
                throw new Exception("<= expected: " + t);

            // Upper bound
            t = scanner.nextToken();
            if (t.Type != TokenType.Integer && t.Type != TokenType.Double)
                throw new Exception("A number is expected: " + t);

            decimal high = decimal.Parse(t.StringValue);

            lp.vars.AddVariable(varName);
            lp.vars[varName].LBound = low;
            lp.vars[varName].UBound = high;
        }


        /// <summary>
        /// Parses a LP
        /// </summary>
        /// <param name="scanner"></param>
        /// <returns></returns>
        public static LP ParseLP(Scanner scanner)
        {
            LP lp = new LP();

            // Maximize
            Token t = scanner.nextToken();
            if (t.Type != TokenType.Identifier && t.StringValue != "Maximize")
                throw new Exception("Maximize expected: " + t);

            // objective
            t = scanner.nextToken();
            if (t.Type != TokenType.Identifier)
                throw new Exception("Identifier expected: " + t);

            // :
            t = scanner.nextToken();
            if (t.Type != TokenType.Colon)
                throw new Exception(": expected: " + t);

            // objective function
            lp.objective = LinearFunction.ParseFunction(scanner);

            // Subject To
            t = scanner.nextToken();
            if (t.Type != TokenType.Identifier && t.StringValue != "Subject")
                throw new Exception("Subject To expected: " + t);

            t = scanner.nextToken();
            if (t.Type != TokenType.Identifier && t.StringValue != "To")
                throw new Exception("Subject To expected: " + t);

            // Constraints
            while (true)
            {
                t = scanner.peekToken();
                if (t.Type == TokenType.Identifier && t.StringValue == "Bounds")
                    break;

                if (t.Type == TokenType.EOF)
                    break;

                Inequality ineq = Inequality.ParseInequality(scanner);
                lp.originalIneqs.Add(ineq);
            }

            // Bounds
            t = scanner.nextToken();
            if (t.Type != TokenType.Identifier && t.StringValue != "Bounds")
                throw new Exception("Bounds expected: " + t);

            // Bounds
            while (true)
            {
                t = scanner.peekToken();
                if (t.Type == TokenType.Identifier && t.StringValue == "End")
                    break;

                if (t.Type == TokenType.EOF)
                    break;

                ParseBound(scanner, lp);
            }

            return lp;
        }
    }
}
