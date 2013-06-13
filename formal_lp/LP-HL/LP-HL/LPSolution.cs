using System;
using System.Collections.Generic;
using System.Linq;
using System.Text;
using System.IO;

namespace LP_HL
{
    /// <summary>
    /// A solution of an LP
    /// </summary>
    class LPSolution
    {
        /// <summary>
        /// Number of constraints
        /// </summary>
        public int NumberOfConstraints { get; private set; }

        /// <summary>
        /// Number of variables
        /// </summary>
        public int NumberOfVariables { get; private set; }

        /// <summary>
        /// The value of an objective function
        /// </summary>
        public LpNumber Optimal { get; private set; }

        /// <summary>
        /// The desired upper bound
        /// </summary>
        public LpNumber UpperBound { get; private set; }


        /// <summary>
        /// Marginals for constraints
        /// </summary>
        public List<LpNumber> ConstraintMarginals { get; private set; }

        /// <summary>
        /// Marginals for variables
        /// </summary>
        public List<LpNumber> VariableMarginals {get; private set; }


        /// <summary>
        /// Private constructor
        /// </summary>
        private LPSolution()
        {
            ConstraintMarginals = new List<LpNumber>();
            VariableMarginals = new List<LpNumber>();
        }


        /// <summary>
        /// Reads k third values from the input stream
        /// </summary>
        /// <param name="k"></param>
        /// <returns></returns>
        private static List<LpNumber> ReadThirdValue(StreamReader r, int k, int precision)
        {
            List<LpNumber> result = new List<LpNumber>();

            for (int i = 0; i < k; i++)
            {
                string str = r.ReadLine();
                if (str == null)
                    throw new Exception("Unexpected end of file");

                string[] els = str.Split(' ');
                if (els.Length != 3)
                    throw new Exception("Triples are expected: " + str);

                LpNumber val = new LpNumber(double.Parse(els[2]), precision);
                result.Add(val);
            }

            return result;
        }


        /// <summary>
        /// Loads solutions from a stream (a file)
        /// </summary>
        /// <param name="r"></param>
        /// <returns></returns>
        public static LPSolution LoadSolution(StreamReader r, int precision, LpNumber upperBound, bool infeasible)
        {
            LPSolution sol = new LPSolution();
            sol.UpperBound = upperBound;

            if (infeasible)
            {
                sol.UpperBound = new LpNumber(0);
            }

            string str = r.ReadLine();
            if (str == null)
                throw new Exception("Two numbers are expected on the first line");

            string[] els = str.Split(' ');
            if (els.Length != 2)
                throw new Exception("Two numbers are expected on the first line");

            int nc = int.Parse(els[0]);
            int nv = int.Parse(els[1]);

            if (infeasible)
            {
                sol.NumberOfConstraints = nc;
                // Do not count slack variables
                sol.NumberOfVariables = nv - nc;
            }
            else
            {
                // Subtract one since we don't count the objective function for a feasible solution
                sol.NumberOfConstraints = nc - 1;
                sol.NumberOfVariables = nv;
            }

            // Optimal
            var vals = ReadThirdValue(r, 1, precision);
            sol.Optimal = vals[0];

            if (!infeasible)
            {
                // Skip one line (the objective function)
                ReadThirdValue(r, 1, precision);
            }

            // Constraints
            sol.ConstraintMarginals = ReadThirdValue(r, sol.NumberOfConstraints, precision);

            if (infeasible)
            {
                // Skip slack variables
                ReadThirdValue(r, nc, precision);
            }

            // Bounds
            sol.VariableMarginals = ReadThirdValue(r, sol.NumberOfVariables, precision);

            return sol;
        }
    }
}
