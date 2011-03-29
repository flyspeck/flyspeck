using System;
using System.Collections.Generic;
using System.Linq;
using System.Text;

namespace LP_HL
{
    /// <summary>
    /// A variable
    /// </summary>
    class Variable
    {
        public Label Name { get; private set; }

        /// <summary>
        /// Lower bound
        /// </summary>
        public decimal LBound { get; set; }

        /// <summary>
        /// Upper bound.
        /// </summary>
        public decimal UBound { get; set; }

        /// <summary>
        /// Marginal for the lower bound
        /// </summary>
        public LpNumber LMarginal { get; set; }

        /// <summary>
        /// Marginal for the upper bound
        /// </summary>
        public LpNumber UMarginal { get; set; }


        /// <summary>
        /// Indicates that the variable is in the objective function
        /// </summary>
        public bool TargetVariable { get; set; }


        /// <summary>
        /// Creates a variable with the given name
        /// </summary>
        /// <param name="name"></param>
        public Variable(Label name)
        {
            this.Name = name;
            this.LBound = decimal.MinValue;
            this.UBound = decimal.MaxValue;
            this.LMarginal = new LpNumber(0);
            this.UMarginal = new LpNumber(0);
        }


        /// <summary>
        /// Changes the index of the variable
        /// </summary>
        /// <param name="hypermap"></param>
        public void Relabel(ListHyp hypermap)
        {
            // No index
            if (Name.index == "")
                return;

            HypermapElement element = hypermap.Manager.TranslateVariable(hypermap, Name);
            Name = new Label(Name.name, element.ToString());
        }


        /// <summary>
        /// Concatenates name and index
        /// </summary>
        public void SimplifyName()
        {
            string newName = Name.name;

            if (Name.index != null && Name.index.Length > 0)
                newName += "_" + Name.index.Replace(',', '_');
            
            Name = new Label(newName, "");
        }


        /// <summary>
        /// ToString()
        /// </summary>
        /// <returns></returns>
        public override string ToString()
        {
            if (TargetVariable)
                return "zz_" + Name;
            else
                return Name.ToString();
        }

    }


    /// <summary>
    /// A collection of variables
    /// </summary>
    class VariableCollection
    {
        // All variables
        private Dictionary<Label, Variable> vars;
        // List of the variables in the order of appearance
        private List<Variable> varList;

        // Variable can be relabeled only once
        private bool relabeledFlag;


        /// <summary>
        /// Default constructor
        /// </summary>
        public VariableCollection()
        {
            this.vars = new Dictionary<Label, Variable>();
            this.varList = new List<Variable>();
            this.relabeledFlag = false;
        }


        /// <summary>
        /// Changes indices of all variables using the given hypermap
        /// </summary>
        /// <param name="hypermap"></param>
        public void RelabelAllVariables(ListHyp hypermap)
        {
            if (relabeledFlag)
                return;

            relabeledFlag = true;

            int n = varList.Count;
            for (int i = 0; i < n; i++)
            {
                try
                {
                    varList[i].Relabel(hypermap);
                }
                catch (Exception e)
                {
                    Console.WriteLine(e);
                    throw e;
                }
            }
        }


        /// <summary>
        /// Concatenates names and indices of variables into new names
        /// </summary>
        public void MakeSimpleNames()
        {
            foreach (var v in varList)
                v.SimplifyName();
        }


        /// <summary>
        /// Adds a new variable to the collection
        /// </summary>
        /// <param name="name"></param>
        public void AddVariable(Label name)
        {
            if (vars.ContainsKey(name))
                throw new Exception("Variable " + name + " is already defined");

            Variable var = new Variable(name);
            vars.Add(name, var);
            varList.Add(var);
        }


        /// <summary>
        /// Returns the number of variables in the collection
        /// </summary>
        public int Number { get { return varList.Count; } }

        /// <summary>
        /// Returns the i-th variable
        /// </summary>
        /// <param name="i"></param>
        /// <returns></returns>
        public Variable this[int i]
        {
            get
            {
                return varList[i];
            }
        }

        /// <summary>
        /// Returns a variable by its name
        /// </summary>
        /// <param name="name"></param>
        /// <returns>null if no variable with the given name is defined</returns>
        public Variable this[Label name]
        {
            get
            {
                if (vars.ContainsKey(name))
                    return vars[name];
                return null;
            }
        }
    }
}
