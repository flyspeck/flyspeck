using System;
using System.Collections.Generic;
using System.Linq;
using System.Text;
using System.IO;

namespace LP_HL
{
    /// <summary>
    /// A hypermap of a list
    /// </summary>
    class ListHyp
    {
        // Manager of hypermaps
        public ListHypManager Manager { get; private set; }

        // Raw data
        public readonly string rawString;

        // Main data
        private readonly List<List<int>> list;

        /// <summary>
        /// Hypermap's id
        /// </summary>
        public string Id { get; private set; }

        // Sets of elements of the hypermap
        private Dictionary<string, List<HypermapElement>> sets;

        // Tables for translation between mod-file definitions and
        // hypermap definitions.
        // First key: a category name (e-dart, node, etc.)
        // Second key: the value of a mod-file element ((1,2,3,0) for e-dart, etc)
        private Dictionary<string, Dictionary<string, HypermapElement>> translationTables;


        /// <summary>
        /// Creates a list hypermap from its string representation
        /// </summary>
        /// <param name="str"></param>
        public ListHyp(string str, ListHypManager manager)
        {
            this.Manager = manager;
            this.rawString = str;
            this.list = new List<List<int>>();

            string[] els = str.Split(' ');
            this.Id = els[0];

            for (int i = 2; i < els.Length;)
            {
                string el = els[i++];
                if (el == null || el == "")
                    continue;

                int n = int.Parse(el);
                List<int> face = new List<int>();

                for (int k = 0; k < n; k++)
                {
                    el = els[i++];
                    face.Add(int.Parse(el));
                }

                list.Add(face);
            }
        }


        /// <summary>
        /// Translates a mod-element (e_dart, node, etc.) of the given type
        /// (e_dart, node, face, etc.) into a corresponding hypermap element
        /// </summary>
        /// <param name="modElement"></param>
        /// <returns>null if no appropriate translation is defined</returns>
        public HypermapElement Translate(string type, string modElement)
        {
            if (translationTables == null)
                return null;

            if (!translationTables.ContainsKey(type))
                return null;

            return translationTables[type][modElement];
        }


        /// <summary>
        /// Finds the index of the given element in the specific set
        /// </summary>
        /// <param name="setName"></param>
        /// <param name="element"></param>
        /// <returns></returns>
        public int FindElementIndex(string setName, HypermapElement element)
        {
            var set = sets[setName];
            return set.IndexOf(element);
        }


        /// <summary>
        /// Creates a list of pairs
        /// </summary>
        private List<Dart> ListPairs(List<int> l)
        {
            List<Dart> result = new List<Dart>();

            int n = l.Count;
            for (int i = 0; i < n; i++)
            {
                int i1 = (i + 1 < n) ? i + 1 : 0;
                result.Add(new Dart(l[i], l[i1]));
            }

            return result;
        }


        /// <summary>
        /// Finds the face which contains the given dart
        /// </summary>
        private int FindFaceIndex(int i1, int i2)
        {
            for (int j = 0; j < list.Count; j++)
            {
                var f = list[j];
                int n = f.Count;
                for (int i = 0; i < n; i++)
                {
                    if (f[i] == i1 && f[(i + 1) % n] == i2)
                        return j;
                }
            }

            return -1;
        }


        /// <summary>
        /// Computes all sets of darts
        /// </summary>
        public void ComputeAllSets()
        {
            // faces
            var faces = list.map(l => ListPairs(l));
            var faces3 = faces.filter(f => f.Count == 3);
            var faces4 = faces.filter(f => f.Count == 4);
            var faces5 = faces.filter(f => f.Count == 5);
            var faces6 = faces.filter(f => f.Count == 6);

            // darts
            var darts = faces.flatten();
            var darts3 = faces3.flatten();
            var darts4 = faces4.flatten();
            var dartsX = faces.filter(f => f.Count >= 4).flatten();

            // edges
            var edges = darts.map(d => new List<Dart>(new Dart[] {d, new Dart(d.b, d.a)} ));
            
            // nodes
            var elements = list.flatten().removeDuplicates();
            var nodes = elements.map(x => darts.filter(d => d.a == x));


            // Add everything to the collection of all sets
            sets = new Dictionary<string, List<HypermapElement>>();

            sets.Add("faces", faces.ToHypermapElements());
            sets.Add("darts", darts.ToHypermapElements());
            sets.Add("edges", edges.ToHypermapElements());
            sets.Add("nodes", nodes.ToHypermapElements());
            sets.Add("darts3", darts3.ToHypermapElements());
            sets.Add("darts4", darts4.ToHypermapElements());
            sets.Add("dartsX", dartsX.ToHypermapElements());
            sets.Add("faces3", faces3.ToHypermapElements());
            sets.Add("faces4", faces4.ToHypermapElements());
            sets.Add("faces5", faces5.ToHypermapElements());
            sets.Add("faces6", faces6.ToHypermapElements());

            // Special names
            sets.Add("dart_std4", sets["darts4"]);
            sets.Add("dart3", sets["darts3"]);
            sets.Add("dart_std3", sets["darts3"]);
            sets.Add("dart_std", sets["darts"]);
            sets.Add("std3", sets["faces3"]);
            sets.Add("std4", sets["faces4"]);
            sets.Add("std5", sets["faces5"]);
            sets.Add("std6", sets["faces6"]);
            sets.Add("dartX", sets["dartsX"]);

            // Create the translation tables
            translationTables = new Dictionary<string, Dictionary<string, HypermapElement>>();

            // e_darts, faces, darts
            Dictionary<string, HypermapElement> e_darts = new Dictionary<string, HypermapElement>();
            Dictionary<string, HypermapElement> mod_faces = new Dictionary<string,HypermapElement>();
            Dictionary<string, HypermapElement> mod_darts = new Dictionary<string,HypermapElement>();

            for (int j = 0; j < list.Count; j++)
            {
                var f = list[j];
                int n = f.Count;
                for (int i = 0; i < n; i++)
                {
                    int i1 = f[i];
                    int i2 = f[(i + 1) % n];
                    int i3 = f[(i + 2) % n];
                    string e_dart = i1 + "," + i2 + "," + i3 + "," + j;
                    string dart = i2 + "," + j;
                    HypermapElement d = new Dart(i2, i3);

                    e_darts.Add(e_dart, d);
                    mod_darts.Add(dart, d);
                }

                mod_faces.Add(j.ToString(), new DartList(faces[j]));
            }

            // nodes
            Dictionary<string, HypermapElement> mod_nodes = new Dictionary<string, HypermapElement>();
            foreach (int x in elements)
            {
                mod_nodes.Add(x.ToString(), new DartList(darts.filter(d => d.a == x)));
            }

            // edges
            Dictionary<string, HypermapElement> mod_edges = new Dictionary<string, HypermapElement>();
            foreach (var e in edges)
            {
                Dart d1 = e[0];
                Dart d2 = e[1];
                int i1 = d1.a;
                int j1 = FindFaceIndex(d1.a, d1.b);

                int i2 = d2.a;
                int j2 = FindFaceIndex(d2.a, d2.b);

                string edge = i1 + "," + j1 + "," + i2 + "," + j2;
                mod_edges.Add(edge, new DartList(e));
            }


            // Add everything into the global table
            translationTables.Add("e_dart", e_darts);
            translationTables.Add("dart", mod_darts);
            translationTables.Add("edge", mod_edges);
            translationTables.Add("face", mod_faces);
            translationTables.Add("node", mod_nodes);
        }


    }


    /// <summary>
    /// Manages hypermaps
    /// </summary>
    class ListHypManager
    {
        // Data
        private Dictionary<string, ListHyp> data;

        /// <summary>
        /// Auxiliary class
        /// </summary>
        private class Definition
        {
            public string name;
            public string domain;
            public string set;

            public Definition(string name, string domain, string set)
            {
                this.name = name;
                this.domain = domain;
                this.set = set;
            }

            public Definition(string name, string domain) :
                this(name, domain, null)
            {
            }

            public override string ToString()
            {
                return name + ": " + domain + ", " + set;
            }
        }


        // Definitions for constraints
        private Dictionary<string, Definition> constraints;
        // Definitions for variables
        private Dictionary<string, Definition> variables;

        // Default sets for domains (node: nodes, etc.)
        private Dictionary<string, string> defaultSets;


        /// <summary>
        /// Reads all hypermaps from a file
        /// </summary>
        public ListHypManager(TextReader tame_archive, TextReader definitions)
        {
            // Load all hypermaps
            data = new Dictionary<string, ListHyp>();

            while (true)
            {
                string str = tame_archive.ReadLine();
                if (str == null)
                    break;

                if (str.Length < 2)
                    continue;

                if (str[0] != '"')
                    continue;

                str = str.Substring(1, str.Length - 3);
                ListHyp hyp = new ListHyp(str, this);

                data.Add(hyp.Id, hyp);
            }

            // Load definitions
            Scanner s = new Scanner(definitions);
            Token t;

            // DefaultSets
            t = s.nextToken();
            if (t.StringValue != "DefaultSets")
                throw new Exception("DefaultSets expected: " + t);

            LoadDefaultSets(s);

            // Variable
            t = s.nextToken();
            if (t.StringValue != "Variables")
                throw new Exception("Variables expected: " + t);

            LoadVariables(s);

            // Constraints
            t = s.nextToken();
            if (t.StringValue != "Constraints")
                throw new Exception("Constraints expected: " + t);

            LoadConstraints(s);
            GenerateVariableInequalities();
        }


        /// <summary>
        /// Returns a hypermap element corresponding to the variable name
        /// </summary>
        /// <param name="varName"></param>
        /// <returns></returns>
        public HypermapElement TranslateVariable(ListHyp hypermap, Label varName)
        {
            string domain = variables[varName.name].domain;
            return hypermap.Translate(domain, varName.index);
        }


        public HypermapElement TranslateIneq(ListHyp hypermap, Label ineqId)
        {
            string domain = constraints[ineqId.name].domain;
            return hypermap.Translate(domain, ineqId.index);
        }


        public int FindIneqIndex(ListHyp hypermap, Label ineqId)
        {
            Definition c = constraints[ineqId.name];
            HypermapElement element = hypermap.Translate(c.domain, ineqId.index);
            return hypermap.FindElementIndex(c.set, element);
        }


        /// <summary>
        /// Generates inequalities for bounds of variables
        /// </summary>
        private void GenerateVariableInequalities()
        {
            var vars = variables.Keys;
            foreach (string name in vars)
            {
                Definition var = variables[name];
                Definition c_lo = new Definition(var.name + "_lo", var.domain, var.set);
                Definition c_hi = new Definition(var.name + "_hi", var.domain, var.set);
                constraints.Add(c_lo.name, c_lo);
                constraints.Add(c_hi.name, c_hi);
            }
        }



        // Loads constraints
        private void LoadConstraints(Scanner s)
        {
            constraints = new Dictionary<string, Definition>();

            while (true)
            {
                Token t = s.peekToken();
                if (t.Type == TokenType.EOF)
                    break;

                if (t.Type == TokenType.Identifier && t.StringValue == "end")
                {
                    // end
                    s.nextToken();
                    break;
                }

                Definition def = ReadDefinition(s);
                if (def.set == null)
                    def.set = defaultSets[def.domain];

                constraints.Add(def.name, def);
            }
        }
        


        // Loads default sets
        private void LoadDefaultSets(Scanner s)
        {
            defaultSets = new Dictionary<string, string>();

            while (true)
            {
                Token t = s.peekToken();
                if (t.Type == TokenType.EOF)
                    break;

                if (t.Type == TokenType.Identifier && t.StringValue == "end")
                {
                    // end
                    s.nextToken();
                    break;
                }

                Definition def = ReadDefinition(s);
                defaultSets.Add(def.name, def.domain);
            }
        }


        // Loads definitions for variables
        private void LoadVariables(Scanner s)
        {
            variables = new Dictionary<string, Definition>();

            while (true)
            {
                Token t = s.peekToken();
                if (t.Type == TokenType.EOF)
                    break;

                if (t.Type == TokenType.Identifier && t.StringValue == "end")
                {
                    // end
                    s.nextToken();
                    break;
                }

                Definition def = ReadDefinition(s);
                if (def.set == null)
                    def.set = defaultSets[def.domain];

                variables.Add(def.name, def);
            }
        }


 


        private Definition ReadDefinition(Scanner s)
        {
            // name
            Token t = s.nextToken();
            if (t.Type != TokenType.Identifier)
                throw new Exception("Identifier expected: " + t);

            string name = t.StringValue;

            // :
            t = s.nextToken();
            if (t.Type != TokenType.Colon)
                throw new Exception(": expected: " + t);

            // domain
            t = s.nextToken();
            if (t.Type != TokenType.Identifier)
                throw new Exception("Identifier expected: " + t);

            string domain = t.StringValue;
            string set = null;

            t = s.peekToken();
            if (t.Type == TokenType.Comma)
            {
                // ,
                t = s.nextToken();
                // set
                t = s.nextToken();
                if (t.Type != TokenType.Identifier)
                    throw new Exception("Identifier expected: " + t);

                set = t.StringValue;
            }

            return new Definition(name, domain, set);
        }


        /// <summary>
        /// Returns a hypermap by its id
        /// </summary>
        /// <param name="id"></param>
        /// <returns></returns>
        public ListHyp this[string id]
        {
            get
            {
                return data[id];
            }
        }
    }
}
