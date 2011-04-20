package edu.pitt.math.jhol.core;

public class Pair<T, U> {
	private final T first;
	private final U second;
	private transient final int hash;

	public Pair(T f, U s) {
		this.first = f;
		this.second = s;
		hash = (first == null ? 0 : first.hashCode() * 31)
				+ (second == null ? 0 : second.hashCode());
	}

	public T getFirst() {
		return first;
	}

	public U getSecond() {
		return second;
	}

	@Override
	public int hashCode() {
		return hash;
	}

	@SuppressWarnings("unchecked")
	@Override
	public boolean equals(Object oth) {
		if (this == oth) {
			return true;
		}
		if (oth == null || !(getClass().isInstance(oth))) {
			return false;
		}
		Pair<T, U> other = getClass().cast(oth);
		return (first == null ? other.first == null : first.equals(other.first))
				&& (second == null ? other.second == null : second
						.equals(other.second));
	}
	
	
	@Override
	public String toString() {
		StringBuilder str = new StringBuilder();
		str.append('(');
		str.append(first);
		str.append(',');
		str.append(second);
		str.append(')');
		
		return str.toString();
	}

}
