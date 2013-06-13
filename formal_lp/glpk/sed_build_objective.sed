/Subject To/ {
	s/.*/m/
	h
}

/:/ {
	x
	s/m/m/
	t continue
	b end
:continue
	x
	s/^\([^:]*\).*/\1/
	H
:end
}

$ {
	x
	s/m//
	s/\n/ -/g
	w objective.txt
}