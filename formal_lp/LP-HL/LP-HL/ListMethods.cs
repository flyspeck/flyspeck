using System;
using System.Collections.Generic;
using System.Linq;
using System.Text;

namespace LP_HL
{
    /// <summary>
    /// List extension methods
    /// </summary>
    static class ListMethods
    {
        /// <summary>
        /// Returns an enumerator for the range [a,b)
        /// </summary>
        public static IEnumerable<int> Range(int a, int b)
        {
            for (int i = a; i < b; i++)
                yield return i;
        }

        /// <summary>
        /// Returns an enumerator for the range [0,n)
        /// </summary>
        public static IEnumerable<int> Range(int n)
        {
            return Range(0, n);
        }

        /// <summary>
        /// Flattens a list
        /// </summary>
        public static List<T> flatten<T>(this List<List<T>> ll)
        {
            List<T> result = new List<T>();
            for (int i = 0; i < ll.Count; i++)
            {
                result.AddRange(ll[i]);
            }

            return result;
        }

        /// <summary>
        /// Filters a list
        /// </summary>
        public static List<T> filter<T>(this List<T> l, Func<T, bool> f)
        {
            List<T> result = (from x in l where f(x) select x).ToList();
            return result;
        }

        /// <summary>
        /// Map function
        /// </summary>
        public static List<R> map<T,R>(this List<T> l, Func<T,R> f)
        {
            return (from x in l select f(x)).ToList();
        }


        /// <summary>
        /// Removes duplicates from a list
        /// </summary>
        public static List<T> removeDuplicates<T>(this List<T> l)
        {
            List<T> result = new List<T>();

            for (int i = 0; i < l.Count; i++)
            {
                T a = l[i];

                for (int j = i + 1; j < l.Count; j++)
                    if (l[j].Equals(a))
                        goto Continue;

                result.Add(a);

            Continue: ;
            }

            return result;
        }


        /// <summary>
        /// Converts a list of darts into a list of hypermap elements
        /// </summary>
        /// <param name="list"></param>
        /// <returns></returns>
        public static List<HypermapElement> ToHypermapElements(this List<Dart> list)
        {
            List<HypermapElement> result = new List<HypermapElement>();
            foreach (var x in list)
            {
                result.Add(x);
            }

            return result;
        }


        /// <summary>
        /// Converts a list of lists of darts into a list of hypermap elements
        /// </summary>
        /// <param name="list"></param>
        /// <returns></returns>
        public static List<HypermapElement> ToHypermapElements(this List<List<Dart>> list)
        {
            List<HypermapElement> result = new List<HypermapElement>();
            foreach (var x in list)
            {
                result.Add(new DartList(x));
            }

            return result;
        }
    }
}
