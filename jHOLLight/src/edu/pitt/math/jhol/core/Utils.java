package edu.pitt.math.jhol.core;

import java.util.List;

/**
 * Contains utility functions
 */
public class Utils {
	/**
	 * assoc
	 */
	public static <T, U> U assoc(T x, List<Pair<T, U>> list) {
		if (list == null)
			return null;
		
		for (Pair<T,U> y : list) {
			T first = y.getFirst();
			if (x == null) {
				if (first == null)
					return y.getSecond();
			}
			else {
				if (x.equals(first))
					return y.getSecond();
			}
		}
		
		return null;
	}
	
	
	/**
	 * rev_assoc
	 */
	public static <T, U> T rev_assoc(U x, List<Pair<T, U>> list) {
		if (list == null)
			return null;
		
		for (Pair<T,U> y : list) {
			U second = y.getSecond();
			if (x == null) {
				if (second == null)
					return y.getFirst();
			}
			else {
				if (x.equals(second))
					return y.getFirst();
			}
		}
		
		return null;
	}
}
