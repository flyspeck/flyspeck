using System;
using System.Collections.Generic;
using System.Linq;
using System.Text;
using System.IO;

namespace LP_HL
{
    /// <summary>
    /// Output methods for LP
    /// </summary>
    partial class LP
    {
        /// <summary>
        /// Compares two inequalities
        /// </summary>
        private class VarsComparer : IComparer<Inequality>
        {
            private VariableCollection vars;

            public VarsComparer(VariableCollection vars)
            {
                this.vars = vars;
            }


            /// <summary>
            /// Special comparison for strings
            /// </summary>
            /// <param name="s1"></param>
            /// <param name="s2"></param>
            /// <returns></returns>
            public int Compare(string s1, string s2)
            {
                int min = Math.Min(s1.Length, s2.Length);

                for (int i = 0; i < min; i++)
                {
                    if (s1[i] < s2[i])
                        return -1;
                    else if (s1[i] > s2[i])
                        return 1;
                }

                if (s1.Length == s2.Length)
                    return 0;

                if (s1.Length < s2.Length)
                    return -1;
                else
                    return 1;
            }


            public int Compare(Inequality x, Inequality y)
            {
                Variable v1 = vars[x.lhs.Terms.First().varName];
                Variable v2 = vars[y.lhs.Terms.First().varName];

                if (v1.TargetVariable)
                {
                    if (v2.TargetVariable)
                        return Compare(v1.Name.ToString(), v2.Name.ToString());
                    else
                        return -1;
                }

                if (v2.TargetVariable)
                    return 1;

                return Compare(v1.Name.ToString(), v2.Name.ToString());
            }
        }


        // Auxiliary class which contains an inequality with index
        private class IndexedInequality : IComparable<IndexedInequality>
        {
            public readonly Inequality ineq;
            public readonly LpNumber marginal;
            public readonly int index;

            /// <summary>
            /// Computes the index automatically
            /// </summary>
            public IndexedInequality(Inequality ineq, LpNumber marginal, ListHyp hypermap)
            {
                this.ineq = ineq;
                this.marginal = marginal;
                this.index = hypermap.Manager.FindIneqIndex(hypermap, ineq.Id);
            }


            public int CompareTo(IndexedInequality other)
            {
                return index.CompareTo(other.index);
            }
        }


        // Auxiliary dictionary
        private Dictionary<string, List<IndexedInequality>> dict = new Dictionary<string, List<IndexedInequality>>();
        // Names are stored separately to preserve the order of inequalities
        private List<string> ineqNames = new List<string>();


        // Adds an indexed inequality to a dictionary
        private void AddIndexedIneq(Inequality ineq, LpNumber marginal, ListHyp hypermap)
        {
            IndexedInequality newIneq = new IndexedInequality(ineq, marginal, hypermap);
            string name = ineq.Id.name;

            // Ad hoc treatment of sums over faces
            if (name == "sol_sum" || name == "tau_sum")
            {
                DartList face = hypermap.Manager.TranslateIneq(hypermap, ineq.Id) as DartList;
                if (face == null)
                    throw new Exception("A face is expected for the constraint " + name);

                name += face.list.Count.ToString();
            }

            if (ineq.type == Inequality.IneqType.Eq && ineq.NegFlag)
                name += "_neg";

            if (dict.ContainsKey(name))
            {
                dict[name].Add(newIneq);
            }
            else
            {
                var list = new List<IndexedInequality>();
                list.Add(newIneq);
                dict.Add(name, list);
                ineqNames.Add(name);
            }
        }


        // Saves all indexed inequalities
        private void SaveIndexedIneqs(StreamWriter writer, int precision, bool holTerms)
        {
            foreach (string name in ineqNames)
            {
                var list = dict[name];
                list.Sort();

                writer.Write("(\"" + name + "\", [");
                for (int i = 0; i < list.Count; i++)
                {
                    writer.Write(list[i].index + "; ");
                }

                writer.Write("], [");
                for (int i = 0; i < list.Count; i++)
                {
                    string str = holTerms ? list[i].marginal.ToHOLExplicit(precision)
                        : list[i].marginal.ToInt64String(precision);
                    writer.Write(str + "; ");
                }

                writer.WriteLine("]);");
            }
        }


        /// <summary>
        /// Creates a HOL certificate
        /// </summary>
        public void PrintCertificate(StreamWriter writer, int precision, ListHyp hypermap, StreamWriter log, bool holTerms)
        {
            // Find target variables
            foreach (var term in objective.Terms)
            {
                vars[term.varName].TargetVariable = true;
            }

            // Compute the precision constant
            decimal mul = 1;
            for (int i = 0; i < precision; i++)
                mul *= 10;

            // Head
//            writer.WriteLine("needs \"nobranching_lp.hl\";;\n");
//            writer.WriteLine("module Test_case = struct");

            // Parameters
            writer.WriteLine("precision := " + precision + ";;");

            dict.Clear();
            ineqNames.Clear();

            // Constraints
            int counter = 0;
            vars.RelabelAllVariables(hypermap);

            writer.WriteLine("(***************)");
            writer.WriteLine("(* Constraints *)");
            writer.WriteLine("(***************)");

            for (int i = 0; i < ineqs.Count; i++)
            {
                Inequality ineq = ineqs[i];
                LpNumber m = ineq.Marginal;

                if (ineq.Id.name == "lnsum_def")
                    throw new Exception("lnsum_def cannot be active");

                // Ignore zero values
                if (m.IsZero(precision))
                    continue;

                ineq *= mul;
                m *= mul;
                AddIndexedIneq(ineq, m, hypermap);
            }

            writer.WriteLine("constraints := [");
            SaveIndexedIneqs(writer, precision, holTerms);
            writer.WriteLine("];;");

            // Variables
            writer.WriteLine();
            writer.WriteLine("(***************)");
            writer.WriteLine("(* Variables   *)");
            writer.WriteLine("(***************)");


            // Sort variables
            varIneqs.Sort(new VarsComparer(vars));

            // Target variables first
            dict.Clear();
            ineqNames.Clear();
            counter = 0;
            for (; counter < varIneqs.Count; counter++)
            {
                Inequality ineq = varIneqs[counter];
                if (!vars[ineq.lhs.Terms.First().varName].TargetVariable)
                    break;

                LpNumber m = ineq.Marginal;

                m *= mul * mul;
                ineq = ineq * mul;

                AddIndexedIneq(ineq, m, hypermap);
            }

            writer.WriteLine("target_variables := [");
            SaveIndexedIneqs(writer, precision, holTerms);
            writer.WriteLine("];;");

            writer.WriteLine();
            writer.WriteLine("(*************************)");
            writer.WriteLine();

            // All other variables
            dict.Clear();
            ineqNames.Clear();

            for (int i = counter; i < varIneqs.Count; i++)
            {
                Inequality ineq = varIneqs[i];
                LpNumber m = ineq.Marginal;

                m *= mul * mul;
                ineq = ineq * mul;

                AddIndexedIneq(ineq, m, hypermap);
            }

            writer.WriteLine("variable_bounds := [");
            SaveIndexedIneqs(writer, precision, holTerms);
            writer.WriteLine("];;");

            // Tail
//            writer.WriteLine("let result = prove_hypermap_lp hypermap_string precision constraints target_variables variable_bounds;;");
//            writer.WriteLine("end;;");
//            writer.WriteLine();
//            writer.WriteLine("concl (Test_case.result)");

            writer.Flush();

            log.WriteLine("{0}\t{1}\t{2}", hypermap.Id, ineqs.Count + varIneqs.Count, vars.Number);
        }

        


        /// <summary>
        /// Prints the given inequality into a stream
        /// </summary>
        private void WriteIneqText(Inequality ineq, LpNumber marginal, int precision,
                StreamWriter writer, ListHyp hypermap)
        {
            // Relabel
            HypermapElement element = hypermap.Manager.TranslateIneq(hypermap, ineq.Id);
            int index = hypermap.Manager.FindIneqIndex(hypermap, ineq.Id);

            // Write out
            if (ineq.NegFlag && ineq.type == Inequality.IneqType.Eq)
                writer.Write("-");
            writer.Write(ineq.Id + " & ");
            writer.Write(index + " & ");
            writer.Write(element + ": ");
            writer.Write(ineq.ToHOLString(precision, vars));
            writer.Write("\t (");
            writer.Write(marginal.ToHOLString(precision));
            writer.WriteLine(")");
        }

        /// <summary>
        /// Prints all inequalities in a text file using HOL syntax
        /// </summary>
        /// <param name="writer"></param>
        /// <param name="precision"></param>
        public void PrintAllText(StreamWriter writer, int precision, ListHyp hypermap)
        {
            // Find target variables
            foreach (var term in objective.Terms)
            {
                vars[term.varName].TargetVariable = true;
            }

            // Compute the precision constant
            decimal mul = 1;
            for (int i = 0; i < precision; i++)
                mul *= 10;

            // Target
            writer.WriteLine("target: " + objective.ToHOLString(precision, vars));

            // Precision
            writer.WriteLine("precision_constant: " + mul);

            // Constraints
            int counter = 0;
            vars.RelabelAllVariables(hypermap);

            for (int i = 0; i < ineqs.Count; i++)
            {
                Inequality ineq = ineqs[i];
                LpNumber m = ineq.Marginal;

                if (ineq.Id.name == "lnsum_def")
                    throw new Exception("lnsum_def cannot be active");

                // Ignore zero values
                if (m.IsZero(precision))
                    continue;

                WriteIneqText(ineq * mul, m * mul, precision, writer, hypermap);   
                counter++;
            }

            writer.WriteLine();
            writer.WriteLine("Inequalities for constraints: {0}", counter);
            writer.WriteLine("-------------------------------------------------------");
            writer.WriteLine();

            // Variables

            // Sort variables
            varIneqs.Sort(new VarsComparer(vars));

            // Target variables first
            writer.WriteLine("Target variables:");
            counter = 0;
            for (; counter < varIneqs.Count; counter++)
            {
                Inequality ineq = varIneqs[counter];
                if (!vars[ineq.lhs.Terms.First().varName].TargetVariable)
                    break;

                LpNumber m = ineq.Marginal; //varIneqMarginals[i];

                m *= mul * mul;
                ineq = ineq * mul;

                WriteIneqText(ineq, m, precision, writer, hypermap);
            }

            writer.WriteLine("-------------------------------------------------------");
            writer.WriteLine();

            // All other variables
            writer.WriteLine("Variables:");

            for (int i = counter; i < varIneqs.Count; i++)
            {
                Inequality ineq = varIneqs[i];
                LpNumber m = ineq.Marginal; //varIneqMarginals[i];

                if (m.IsZero(precision))
                    throw new Exception("Unexpected zero");

                /*                            if (i < varIneqs.Count - 1)
                                            {
                                                Inequality ineq2 = varIneqs[i + 1];
                                                LpNumber m2 = ineq2.Marginal;

                                                if (m2.IsZero(precision))
                                                    throw new Exception("Unexpected zero");

                                                if (ineq.lhs.Terms.First().varName == ineq2.lhs.Terms.First().varName)
                                                {
                                                    m *= mul * mul;
                                                    m2 *= mul * mul;
                                                    ineq = ineq * mul;
                                                    ineq2 = ineq2 * mul;

                                                    writer.Write("var2_le_transform (");
                                                    writer.Write(ineq.ToHOLExplicit(precision, vars));
                                                    writer.Write(", ");
                                                    writer.Write(m.ToHOLExplicit(precision));
                                                    writer.Write(") ");

                                                    writer.Write("(");
                                                    writer.Write(ineq2.ToHOLExplicit(precision, vars));
                                                    writer.Write(", ");
                                                    writer.Write(m2.ToHOLExplicit(precision));
                                                    writer.WriteLine(");");

                                                    i++;
                                                    continue;
                                                }
                                            }
                */
                m *= mul * mul;
                ineq = ineq * mul;

                WriteIneqText(ineq, m, precision, writer, hypermap);
            }

            writer.WriteLine("Inequalities for variables: {0}", varIneqs.Count);


            writer.Flush();
        }


        /// <summary>
        /// Converts the LP into HOL data
        /// </summary>
        /// <param name="writer"></param>
        public void ConvertToHOL(StreamWriter writer, int precision)
        {
            // Find target variables
            foreach (var term in objective.Terms)
            {
                vars[term.varName].TargetVariable = true;
            }


            // Compute the precision constant
            decimal mul = 1;
            for (int i = 0; i < precision; i++)
                mul *= 10;

            // Dependencies
            writer.WriteLine("module Lp = struct");
//            writer.WriteLine("needs \"arith/prove_lp.hl\";;");
            //            writer.WriteLine("open Prove_lp;;");


            // Target
            writer.WriteLine("let target = `" + objective.ToHOLString(precision, vars) + "`;;");

            // Target bound
            writer.WriteLine("let target_bound = `" + upperBound.ToHOLString(100) + "`;;");

            // Precision
            //            LpNumber precision_constant = new LpNumber(mul * mul * mul);
            writer.Write("let precision_constant = ");
            writer.Write("Int " + mul);
            //            writer.Write(precision_constant.ToHOLExplicit(0));
            writer.WriteLine(";;");

            // Constraints
            int counter = 0;
            writer.WriteLine("let ineqs = [");

            vars.MakeSimpleNames();

            for (int i = 0; i < ineqs.Count; i++)
            {
                Inequality ineq = ineqs[i];
                LpNumber m = ineq.Marginal; //ineqMarginals[i];

                if (ineq.Id.name == "lnsum_def")
                    throw new Exception("lnsum_def cannot be active");

                // Ignore zero values
                if (m.IsZero(precision))
                    continue;

                //                m *= mul * mul;
                m *= mul;
                ineq = ineq * mul;

                writer.Write("ASSUME (");
                writer.Write(ineq.ToHOLExplicit(precision, vars));
                writer.Write("), ");
                writer.Write(m.ToHOLExplicit(precision));
                writer.WriteLine(";");
                counter++;
            }

            writer.WriteLine("];;");
            int constraintIneqs = counter;

            // Variables

            // Sort variables
            varIneqs.Sort(new VarsComparer(vars));

            // Save target variables first
            writer.WriteLine("let target_vars = [");
            counter = 0;
            for (; counter < varIneqs.Count; counter++)
            {
                Inequality ineq = varIneqs[counter];
                if (!vars[ineq.lhs.Terms.First().varName].TargetVariable)
                    break;

                LpNumber m = ineq.Marginal; //varIneqMarginals[i];

                m *= mul * mul;
                ineq = ineq * mul;

                writer.Write("ASSUME (");
                writer.Write(ineq.ToHOLExplicit(precision, vars));
                writer.Write("), ");
                writer.Write(m.ToHOLExplicit(precision));
                writer.WriteLine(";");
            }
            writer.WriteLine("];;\n\n");

            writer.WriteLine("let var_ineqs = [");

            //           writer.WriteLine("let vars = [");
            //            counter = 0;

            for (int i = counter; i < varIneqs.Count; i++)
            {
                Inequality ineq = varIneqs[i];
                LpNumber m = ineq.Marginal; //varIneqMarginals[i];

                if (m.IsZero(precision))
                    throw new Exception("Unexpected zero");

                if (i < varIneqs.Count - 1)
                {
                    Inequality ineq2 = varIneqs[i + 1];
                    LpNumber m2 = ineq2.Marginal;

                    if (m2.IsZero(precision))
                        throw new Exception("Unexpected zero");

                    if (ineq.lhs.Terms.First().varName == ineq2.lhs.Terms.First().varName)
                    {
                        m *= mul * mul;
                        m2 *= mul * mul;
                        ineq = ineq * mul;
                        ineq2 = ineq2 * mul;

                        writer.Write("var2_le_transform (");
                        writer.Write(ineq.ToHOLExplicit(precision, vars));
                        writer.Write(", ");
                        writer.Write(m.ToHOLExplicit(precision));
                        writer.Write(") ");

                        writer.Write("(");
                        writer.Write(ineq2.ToHOLExplicit(precision, vars));
                        writer.Write(", ");
                        writer.Write(m2.ToHOLExplicit(precision));
                        writer.WriteLine(");");

                        i++;
                        continue;
                    }
                }

                m *= mul * mul;
                ineq = ineq * mul;

                writer.Write("var1_le_transform (");
                writer.Write(ineq.ToHOLExplicit(precision, vars));
                writer.Write(", ");
                writer.Write(m.ToHOLExplicit(precision));
                writer.WriteLine(");");
                //                writer.WriteLine(";");
            }

            writer.WriteLine("];;");
            Console.WriteLine("Inequalities for constraints: {0}", constraintIneqs);
            Console.WriteLine("Inequalities for variables: {0}", varIneqs.Count);
            Console.WriteLine("Number of variables: {0}", vars.Number);
            Console.WriteLine("Total constraints: {0}", constraintIneqs + varIneqs.Count);

            writer.WriteLine("let start = Sys.time();;");

            writer.WriteLine("let result = prove_lp ineqs var_ineqs target_vars target_bound precision_constant;;");
            //            writer.WriteLine("let result = Prove_lp.prove_lp ineqs vars target_bound precision_constant;;");
            writer.WriteLine("end;;");

            writer.WriteLine("Sys.time() -. Lp.start;;");
            //            writer.WriteLine("let done_message = \"{0} done\";;", fname);
            writer.WriteLine("concl (Lp.result);;");


            writer.Flush();
        }

    }
}
