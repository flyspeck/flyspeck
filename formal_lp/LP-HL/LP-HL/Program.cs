using System;
using System.Collections.Generic;
using System.Linq;
using System.Text;
using System.IO;

namespace LP_HL
{
    /// <summary>
    /// Program class
    /// </summary>
    class Program
    {
        // Log
        private static StreamWriter log;

        // Main
        static void Main(string[] args)
        {
            FileStream flog = new FileStream("log.txt", FileMode.Create);
            log = new StreamWriter(flog);

            using (log)
            {
                // GenerateArithTest();
                // return;

                // Flyspeck
                if (args.Length == 0 || args.Length == 1)
                {
                    try
                    {
                        ListHypManager hypermaps = InitializeHypermaps();
                        Console.WriteLine("Processing Flyspeck linear program(s)");
                        Console.WriteLine();

                        if (args.Length == 1)
                        {
                            ProcessFlyspeckLP(args[0], hypermaps);
                        }
                        else
                        {
                            ProcessFlyspeckLPs(hypermaps);
                        }
                    }
                    catch (Exception e)
                    {
                        Console.Error.WriteLine("ERROR: {0}", e.Message);
                    }

                    return;
                }

                // Incorrect number of arguments
                if (args.Length != 2)
                {
                    Console.WriteLine("Usage: LP-HL lp_name upper_bound");
                    Console.WriteLine("Files {lp_name}.lp and {lp_name}.txt must be in the current directory.");
                    Console.WriteLine("{upper_bound} is a decimal number");
                    return;
                }

                // Specific LP
                string name = args[0];
                LpNumber upperBound = new LpNumber(decimal.Parse(args[1]));
                ProcessLP(name, upperBound, null, true);
            }
        }


        /// <summary>
        /// Processes all Flyspeck linear programs in the current directory
        /// </summary>
        static void ProcessFlyspeckLPs(ListHypManager hypermaps)
        {
            // GenerateExamples();
            string[] files = Directory.GetFiles(".", "flyspeck*.txt");
//            FileStream fs = new FileStream("all_tests.hl", FileMode.Create);
//            StreamWriter w = new StreamWriter(fs);


//            w.WriteLine("let start = Sys.time();;");

//            int i = 1;
            foreach (string file in files)
            {
                string name = ProcessFlyspeckLP(file, hypermaps);
//                w.WriteLine("\"Case: {0}/{1}\";;", i++, files.Length);
//                w.WriteLine("let _ = needs \"{0}\" in Sys.time() -. start;;", name + "_out.hl");
                // break;
            }

//            w.Flush();
//            fs.Close();
        }


        /// <summary>
        /// Processes one Flyspeck LP
        /// </summary>
        /// <param name="fname"></param>
        static string ProcessFlyspeckLP(string fname, ListHypManager hypermaps)
        {
            FileStream info = new FileStream(fname, FileMode.Open);

            try
            {
                string name;
                ListHyp hypermap = hypermaps.ComputeHypermap(new StreamReader(info), out name);

                ProcessLP(name, new LpNumber(12), hypermap, false);
                return name;
            }
            finally
            {
                info.Close();
            }
        }


        /// <summary>
        /// Initializes hypermaps of lists
        /// </summary>
        static ListHypManager InitializeHypermaps()
        {
            FileStream ftame = null;
            if (File.Exists("string_archive.txt"))
            {
                ftame = new FileStream("string_archive.txt", FileMode.Open);
            }

            if (!File.Exists("000.txt"))
            {
                throw new Exception("File 000.txt is required for processing Flyspeck linear programs");
            }

            FileStream fdefs = new FileStream("000.txt", FileMode.Open);
            ListHypManager hypermaps = null;

            try
            {
                hypermaps = new ListHypManager(ftame != null ? new StreamReader(ftame) : null, 
                    new StreamReader(fdefs));
            }
            finally
            {
                if (ftame != null)
                {
                    ftame.Close();
                }

                fdefs.Close();
            }

            return hypermaps;
        }




        /// <summary>
        /// Creates files for producing a formal proof for the given linear program.
        /// The precision is selected automatically
        /// </summary>
        static void ProcessLP(string fname, LpNumber upperBound, ListHyp hypermap, bool holTerms)
        {
            Console.WriteLine("Processing {0}...", fname);
            try
            {
                for (int precision = 3; ; precision++)
                {
                    Console.WriteLine("Precision = {0}", precision);

                    if (hypermap != null)
                    {
                        if (ProcessLP(fname, upperBound, precision, hypermap, holTerms))
                            break;
                    }
                    else
                    {
                        if (processLPGeneral(fname, precision, upperBound))
                            break;
                    }
                }
            }
            catch (Exception e)
            {
                Console.Error.WriteLine("ERROR: {0}", e.Message);
//                Console.Error.WriteLine(e.StackTrace);
            }

            Console.WriteLine("done\n");
        }


        /// <summary>
        /// Creates files for a formal proof for a general linear program
        /// </summary>
        static bool processLPGeneral(string fname, int precision, LpNumber upperBound)
        {
            if (precision > 10)
                throw new Exception("Cannot solve the problem (precision > 10): " + fname);

            LP lp;
            LPSolution sol;

            // Load an LP
            FileStream fs = new FileStream(fname + ".lp", FileMode.Open);
            using (fs)
            {
                StreamReader r = new StreamReader(fs);
                Scanner scanner = new Scanner(r, fname + ".lp");

                lp = LP.ParseLP(scanner);
            }

            // Load solutions
            fs = new FileStream(fname + ".txt", FileMode.Open);
            using (fs)
            {
                sol = LPSolution.LoadSolution(new StreamReader(fs), precision, upperBound);
            }

            if (!lp.SetSolution(sol, precision))
                return false;

            // Create a test file containing all inequalities explicitly
            FileStream test = new FileStream(fname + "_test.hl", FileMode.Create);
            lp.ConvertToHOL(new StreamWriter(test), precision);
            test.Close();

            return true;
        }


        /// <summary>
        /// Creates files for producing a formal proof for the given linear program
        /// </summary>
        static bool ProcessLP(string fname, LpNumber upperBound, int precision, ListHyp hypermap, bool holTerms)
        {
            if (precision > 6)
                throw new Exception("Cannot solve the problem: " + fname);

            LP lp;
            LPSolution sol;

            // Load an LP
            FileStream fs = new FileStream(fname + ".lp", FileMode.Open);
            using (fs)
            {
                StreamReader r = new StreamReader(fs);
                Scanner scanner = new Scanner(r, fname + ".lp");

                lp = LP.ParseLP(scanner);
            }

            // Load solutions
            fs = new FileStream(fname + ".txt", FileMode.Open);
            using (fs)
            {
                sol = LPSolution.LoadSolution(new StreamReader(fs), precision, upperBound);
            }

            if (sol.Optimal.value > upperBound.value)
                throw new Exception("Optimal value is greater than " + upperBound.value + ": " + fname);

            if (!lp.SetSolution(sol, precision))
                return false;

            // Create a test file containing all inequalities explicitly
//            FileStream test = new FileStream(fname + "_test.hl", FileMode.Create);
//            lp.ConvertToHOL(new StreamWriter(test), precision);
//            test.Close();

            // Create a certificate file
            FileStream main = new FileStream(fname + "_out.hl", FileMode.Create);
            lp.PrintCertificate(new StreamWriter(main), precision, hypermap, log, holTerms);
            main.Close();

            // Debug file with text inequalities
//            FileStream text = new FileStream(fname + "_text.hl", FileMode.Create);
//            lp.PrintAllText(new StreamWriter(text), precision, hypermap);
//            text.Close();

            return true;
        }


        /// <summary>
        /// Generates a test file
        /// </summary>
        static void GenerateExamples()
        {
            FileStream fs = new FileStream("examples.hl", FileMode.Create);
            StreamWriter w = new StreamWriter(fs);

            Random rnd = new Random(2);
            // Dependencies
            w.WriteLine("needs \"test_explicit.hl\"");
            w.WriteLine("let test = [");

            for (int k = 0; k < 300; k++)
            {
                List<decimal> cs = new List<decimal>();
                List<string> vars = new List<string>();

                int i = rnd.Next(100);
                while (i >= 0)
                {
                    vars.Add('x'.ToString() + "_" + String.Format("{0:000}", i));
                    cs.Add(rnd.Next(1000000000));

                    i -= rnd.Next(10) + 1;
                }

                LinearFunction f = new LinearFunction(cs, vars);
                w.Write(f.ToHOLExplicit(5, null));
                //                w.Write("`" + f.ToHOLString(5) + "`");
                w.WriteLine(";");
            }

            w.WriteLine("];;");
            w.Flush();
            fs.Close();
        }


        /// <summary>
        /// Generates a test for arithmetic
        /// </summary>
        static void GenerateArithTest()
        {
            FileStream fs = new FileStream("arith_test_data.hl", FileMode.Create);
            StreamWriter w = new StreamWriter(fs);
            Random rnd = new Random(0);

            w.WriteLine("let data = [");

            for (int i = 0; i < 1000; i++)
            {
                decimal n1 = rnd.Next(1000000000, 2000000000);
                decimal n2 = rnd.Next(1000000000, 2000000000);

                //                n1 *= rnd.Next(1000000000, 2000000000);
                //                n2 *= rnd.Next(1000000000, 2000000000);

                n1 *= rnd.Next(100000, 500000);
                n2 *= rnd.Next(100000, 500000);

                int x1 = (int)Math.Log10((double)n1);
                int x2 = (int)Math.Log10((double)n2);

                LpNumber m1 = new LpNumber(n1);
                LpNumber m2 = new LpNumber(n2);

                w.Write(m1.ToHOLExplicit(0));
                w.Write(",");
                w.Write(m2.ToHOLExplicit(0));
                if (i < 999)
                    w.Write(";");

                w.Write("(* {0}, {1} *)", x1, x2);
                w.WriteLine();
            }

            w.WriteLine("];;");

            w.Flush();
            fs.Close();
        }
    }
}
