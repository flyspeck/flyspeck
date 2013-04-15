using System;
using System.Collections.Generic;
using System.Linq;
using System.Text;

namespace LP_HL
{
    /// <summary>
    /// An element of a hypermap: a dart, a face, etc.
    /// </summary>
    class HypermapElement
    {
    }


    /// <summary>
    /// A dart of a hypermap
    /// </summary>
    class Dart : HypermapElement
    {
        public readonly int a, b;

        public Dart(int a, int b)
        {
            this.a = a;
            this.b = b;
        }

        public static Dart Parse(String str)
        {
            string[] els = str.Split(',');
            if (els.Length != 2)
                throw new Exception("Dart.Parse(): bad argument: " + str);

            int a = int.Parse(els[0]);
            int b = int.Parse(els[1]);

            return new Dart(a, b);
        }

        public override string ToString()
        {
            return a + "," + b;
        }


        public override bool Equals(object obj)
        {
            Dart d2 = obj as Dart;
            if (d2 == null)
                return false;

            return a == d2.a && b == d2.b;
        }


        public override int GetHashCode()
        {
            return a.GetHashCode() ^ b.GetHashCode();
        }
    }


    /// <summary>
    /// A collection (list) of darts
    /// </summary>
    class DartList : HypermapElement
    {
        public readonly List<Dart> list;

        public DartList(List<Dart> list)
        {
            for (int i = 0; i < list.Count; i++)
                if (list[i] == null)
                    throw new Exception("Element could not be null");

            this.list = list;
        }

        public override string ToString()
        {
            StringBuilder str = new StringBuilder();

            str.Append("{");
            for (int i = 0; i < list.Count; i++)
            {
                str.Append(list[i]);
                if (i < list.Count - 1)
                    str.Append(", ");
            }
            str.Append("}");

            return str.ToString();
        }


        public override bool Equals(object obj)
        {
            DartList list2 = obj as DartList;
            if (list2 == null)
                return false;

            int n = list.Count;
            for (int i = 0; i < n; i++)
            {
                if (!list[i].Equals(list2.list[i]))
                    return false;
            }

            return true;
        }


        public override int GetHashCode()
        {
            int n = list.Count;
            int hash = n.GetHashCode();
            for (int i = 0; i < n; i++)
                hash ^= list[i].GetHashCode();

            return hash;
        }
    }

}
